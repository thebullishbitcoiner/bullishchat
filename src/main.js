import pkg from '../package.json';
import { SimplePool, generateSecretKey, getPublicKey, getEventHash, finalizeEvent } from 'nostr-tools';
import * as nip19 from 'nostr-tools/nip19';
import { decodeInvoice } from '@getalby/lightning-tools/bolt11';
// Note: nip44 is used for both ephemeral key operations and user key operations
// We check if extension provides nip44, otherwise fall back to library (but need private key access)
import { encrypt as nip44Encrypt, decrypt as nip44Decrypt, getConversationKey } from 'nostr-tools/nip44';

// Relay URLs to connect to
const RELAY_URLS = [
    'wss://relay.0xchat.com',
    'wss://relay.damus.io',
    'wss://relay.primal.net'
];

let pool = null;
let publicKey = null;
let conversations = {};
let currentChat = null;
let userProfiles = {}; // Store user profiles (display names, etc.)
let messageSubscription = null; // Store the message subscription
/** Relays used for DM subscribe/publish: default list plus our kind 10050 inbox relays after connect */
let dmRelayUrls = [...RELAY_URLS];
/** Dedupe kind 1059 events across historical query + live subscription (same id from many relays) */
const seenGiftWrapEventIds = new Set();
/** Avoid repeatedly trying broken image URLs (prevents avatar flash/retry loops). */
const brokenAvatarUrls = new Set();
/** Keep stable DOM rows for conversation list to avoid avatar remount flicker. */
const conversationItemEls = new Map();
/** De-dupe rumors that can arrive via sender/receiver copies across relays. */
const seenRumorIds = new Set();
/** Reactions that arrive before their target message. */
const pendingReactionsByMessageId = new Map();
const DEFAULT_QUICK_REACTIONS = ['🤙', '💜', '👍', '😂', '🚀'];
const DEFAULT_EXTRA_REACTIONS = ['🔥', '👏', '🙏', '🎉', '👀', '💯', '🤯', '🥲', '😎', '🤔'];
const CUSTOM_REACTION_SET_KIND = 30030;
const CUSTOM_REACTION_SET_D_TAG = 'bullishchat-reaction-set';
const LIGHTNING_INVOICE_RE = /(lightning:)?(ln(?:bc|tb|bcrt|sb)[0-9a-z]+)/i;
/** Detect bare http(s) URLs in message text for links / inline images (DOM-built, no HTML injection). */
const HTTP_URL_IN_TEXT_RE = /\bhttps?:\/\/[^\s<>"'`]+/gi;
/** Blob URLs for decrypted kind-15 previews — revoked when the message list re-renders. */
const activeMessageBlobUrls = new Set();
const CONVERSATION_REPAIR_LOOKBACK_SECS = 14 * 24 * 60 * 60;
const CONVERSATION_REPAIR_LIMIT = 1200;
const CONVERSATION_REPAIR_COOLDOWN_MS = 15000;
/** Paginated repair: one REQ often caps below total backlog (mobile + multi-relay). */
const REPAIR_MAX_PAGES_DEFAULT = 8;
const REPAIR_MAX_PAGES_DEEP = 14;
const REPAIR_PAGE_LIMIT_DEEP = 1500;
const INCREMENTAL_INBOX_INTERVAL_MS = 45_000;
const INCREMENTAL_INBOX_OVERLAP_SECS = 5 * 60;
const INCREMENTAL_INBOX_PAGE_LIMIT = 400;
const INCREMENTAL_INBOX_MAX_PAGES = 2;
const GAP_FILL_DEBOUNCE_MS = 450;
const GAP_FILL_COOLDOWN_MS = 8000;
const GAP_FILL_MAX_PAGES = 5;

let conversationsListUpdateQueued = false;
function queueConversationsListUpdate() {
    if (conversationsListUpdateQueued) return;
    conversationsListUpdateQueued = true;
    requestAnimationFrame(() => {
        conversationsListUpdateQueued = false;
        updateConversationsList();
    });
}

let chatHeaderUpdateQueued = false;
function queueChatHeaderUpdate(pubkey) {
    if (currentChat !== pubkey || chatHeaderUpdateQueued) return;
    chatHeaderUpdateQueued = true;
    requestAnimationFrame(() => {
        chatHeaderUpdateQueued = false;
        if (currentChat === pubkey) {
            updateChatHeader(pubkey);
        }
    });
}

let activeChatRenderTimer = null;
let activeChatRenderPubkey = null;
let activeChatRenderNeedsHeader = false;
function queueActiveChatRender(pubkey, opts = {}) {
    if (currentChat !== pubkey) return;
    activeChatRenderPubkey = pubkey;
    activeChatRenderNeedsHeader = activeChatRenderNeedsHeader || Boolean(opts.header);
    if (activeChatRenderTimer) return;
    activeChatRenderTimer = setTimeout(() => {
        const target = activeChatRenderPubkey;
        const shouldHeader = activeChatRenderNeedsHeader;
        activeChatRenderTimer = null;
        activeChatRenderPubkey = null;
        activeChatRenderNeedsHeader = false;
        if (!target || currentChat !== target) return;
        displayMessages(target);
        if (shouldHeader) {
            updateChatHeader(target);
        }
    }, 90);
}

/** nostr.wine search (kind 0); free tier ~1 req/s */
const NOSTR_WINE_SEARCH_URL = 'https://api.nostr.wine/search';

let wineSearchAbort = null;
let wineSearchDebounceTimer = null;
let wineSearchSerial = 0;
let lastNostrWineRequestMs = 0;
const conversationRepairLastRunMs = new Map();
/** Per-thread repair so opening chat B is not blocked by chat A. */
const conversationRepairRunning = new Set();
let lastInboxGiftWrapProcessedSec = 0;
let incrementalInboxTimerId = null;
let incrementalInboxInFlight = false;
const gapFillDebounceByConv = new Map();
const gapFillLastRunMs = new Map();
let isInboxLoading = false;
let settingsRelayDraft = [];
let customReactionEmojiSet = [];
let customReactionEmojiUrlMap = {};
let discoveredEmojiSets = [];
let settingsEmojiDraftSet = [];
let mobileCatchupTimer = null;

function splitGraphemes(str) {
    if (!str) return [];
    if (typeof Intl !== 'undefined' && typeof Intl.Segmenter === 'function') {
        const seg = new Intl.Segmenter(undefined, { granularity: 'grapheme' });
        return [...seg.segment(str)].map((s) => s.segment);
    }
    return Array.from(str);
}

function getReactionSet() {
    const list = customReactionEmojiSet.length
        ? customReactionEmojiSet
        : [...DEFAULT_QUICK_REACTIONS, ...DEFAULT_EXTRA_REACTIONS];
    return {
        quick: list.slice(0, 5),
        extra: list.slice(5)
    };
}

function emojiShortcodeFromToken(token) {
    if (typeof token !== 'string') return '';
    const m = token.trim().match(/^:([a-zA-Z0-9_+-]+):$/);
    return m ? m[1] : '';
}

function normalizeCustomEmojiLines(raw) {
    const source = typeof raw === 'string' ? raw : '';
    const lines = source
        .split('\n')
        .map((line) => line.trim())
        .filter(Boolean);
    const out = [];
    const seen = new Set();
    for (const line of lines) {
        const emoji = splitGraphemes(line).join('').trim();
        if (!emoji) continue;
        if (seen.has(emoji)) continue;
        seen.add(emoji);
        out.push(emoji);
    }
    return out.slice(0, 64);
}

function parseCustomReactionSetEvent(ev) {
    if (!ev) return [];
    if (Array.isArray(ev.tags)) {
        const tagShortcodes = ev.tags
            .filter((t) => t[0] === 'emoji' && typeof t[1] === 'string' && t[1].trim().length)
            .map((t) => `:${t[1].trim()}:`);
        if (tagShortcodes.length) {
            return normalizeCustomEmojiLines(tagShortcodes.join('\n'));
        }
    }
    try {
        const parsed = JSON.parse(ev.content || '{}');
        if (Array.isArray(parsed?.emojis)) {
            return normalizeCustomEmojiLines(parsed.emojis.join('\n'));
        }
    } catch {
        // fallback below
    }
    return normalizeCustomEmojiLines(ev?.content || '');
}

function parseCustomReactionSetMeta(ev) {
    if (!ev) return { emojis: [], urlMap: {} };
    const urlMap = {};
    if (Array.isArray(ev.tags)) {
        for (const t of ev.tags) {
            if (t[0] !== 'emoji') continue;
            const shortcode = typeof t[1] === 'string' ? t[1].trim() : '';
            const url = typeof t[2] === 'string' ? t[2].trim() : '';
            if (!shortcode || !url) continue;
            urlMap[shortcode] = url;
        }
        const tagShortcodes = Object.keys(urlMap).map((s) => `:${s}:`);
        if (tagShortcodes.length) {
            return {
                emojis: normalizeCustomEmojiLines(tagShortcodes.join('\n')),
                urlMap
            };
        }
    }
    return {
        emojis: parseCustomReactionSetEvent(ev),
        urlMap: {}
    };
}

function getTagValue(tags, key) {
    if (!Array.isArray(tags)) return '';
    const row = tags.find((t) => t[0] === key && typeof t[1] === 'string' && t[1].length);
    return row ? row[1] : '';
}

function shortAuthor(pubkey) {
    try {
        const npub = nip19.npubEncode(pubkey);
        return `${npub.slice(0, 10)}…${npub.slice(-6)}`;
    } catch {
        return `${pubkey.slice(0, 8)}…${pubkey.slice(-6)}`;
    }
}

function renderDiscoveredEmojiSets() {
    const list = document.getElementById('settingsEmojiDiscoverList');
    if (!list) return;
    list.innerHTML = '';
    if (!discoveredEmojiSets.length) {
        list.innerHTML = '<div class="new-chat-suggestion-empty" role="status">No emoji sets found on connected relays.</div>';
        return;
    }
    for (const set of discoveredEmojiSets) {
        const row = document.createElement('div');
        row.className = 'settings-emoji-set-item';

        const main = document.createElement('div');
        main.className = 'settings-emoji-set-main';
        const name = document.createElement('div');
        name.className = 'settings-emoji-set-name';
        name.textContent = set.name;
        const meta = document.createElement('div');
        meta.className = 'settings-emoji-set-meta';
        const emojiLabel = set.count === 1 ? 'emoji' : 'emojis';
        meta.textContent = `${set.count} ${emojiLabel} · by ${getDisplayName(set.pubkey)}`;
        const preview = document.createElement('div');
        preview.className = 'settings-emoji-set-preview';
        const previewTokens = set.emojis.slice(0, 7);
        for (const token of previewTokens) {
            const shortcode = emojiShortcodeFromToken(token);
            const url = shortcode ? (set.urlMap?.[shortcode] || '') : '';
            if (url) {
                const img = document.createElement('img');
                img.src = url;
                img.alt = token;
                img.referrerPolicy = 'no-referrer';
                img.loading = 'lazy';
                preview.appendChild(img);
            } else if (!shortcode) {
                const span = document.createElement('span');
                span.textContent = token;
                preview.appendChild(span);
            }
        }
        main.appendChild(name);
        main.appendChild(meta);
        main.appendChild(preview);

        const importBtn = document.createElement('button');
        importBtn.type = 'button';
        importBtn.className = 'settings-add-btn';
        importBtn.textContent = 'Import';
        importBtn.addEventListener('click', () => {
            const status = document.getElementById('settingsEmojiStatus');
            customReactionEmojiUrlMap = { ...(set.urlMap || {}) };
            settingsEmojiDraftSet = [...set.emojis];
            renderSettingsEmojiPreview(settingsEmojiDraftSet);
            if (status) status.textContent = `Imported "${set.name}". Save to publish it on your profile.`;
        });

        row.appendChild(main);
        row.appendChild(importBtn);
        list.appendChild(row);
    }
}

async function discoverEmojiSets() {
    const status = document.getElementById('settingsEmojiDiscoverStatus');
    if (status) status.textContent = 'Searching…';
    try {
        const relays = [...new Set([...(dmRelayUrls?.length ? dmRelayUrls : []), ...RELAY_URLS])];
        const filter = { kinds: [CUSTOM_REACTION_SET_KIND], limit: 80 };
        console.log('[emoji-discovery] querying relays:', relays);
        console.log('[emoji-discovery] filter:', filter);
        const events = await pool.querySync(
            relays,
            filter,
            { maxWait: 12000 }
        );
        console.log('[emoji-discovery] raw event count:', Array.isArray(events) ? events.length : 0);
        const newestByKey = new Map();
        for (const ev of events || []) {
            const d = getTagValue(ev.tags, 'd') || 'default';
            const key = `${ev.pubkey}:${d}`;
            const prev = newestByKey.get(key);
            if (!prev || (ev.created_at || 0) > (prev.created_at || 0)) {
                newestByKey.set(key, ev);
            }
        }
        console.log('[emoji-discovery] unique set keys:', newestByKey.size);
        const parsed = [];
        for (const ev of newestByKey.values()) {
            const parsedSet = parseCustomReactionSetMeta(ev);
            const emojis = parsedSet.emojis;
            if (!emojis.length) continue;
            const name = getTagValue(ev.tags, 'name') || getTagValue(ev.tags, 'title') || getTagValue(ev.tags, 'd') || 'Untitled set';
            parsed.push({
                pubkey: ev.pubkey,
                name,
                emojis,
                urlMap: parsedSet.urlMap,
                count: emojis.length,
                createdAt: ev.created_at || 0
            });
        }
        parsed.sort((a, b) => b.createdAt - a.createdAt);
        discoveredEmojiSets = parsed.slice(0, 40);
        if (discoveredEmojiSets.length) {
            console.log(
                '[emoji-discovery] top sets:',
                discoveredEmojiSets.slice(0, 5).map((s) => ({
                    name: s.name,
                    author: s.pubkey,
                    count: s.count
                }))
            );
        } else {
            console.log('[emoji-discovery] no parseable sets found from queried events');
        }
        renderDiscoveredEmojiSets();
        if (status) status.textContent = discoveredEmojiSets.length ? `${discoveredEmojiSets.length} set(s) found.` : 'No sets found.';
    } catch (e) {
        console.error('[emoji-discovery] query failed:', e);
        discoveredEmojiSets = [];
        renderDiscoveredEmojiSets();
        if (status) status.textContent = 'Could not discover emoji sets.';
    }
}

async function loadOwnCustomReactionSetFromNostr() {
    if (!pool || !publicKey) {
        customReactionEmojiSet = [];
        return;
    }
    try {
        const relays = [...new Set([...(dmRelayUrls?.length ? dmRelayUrls : []), ...RELAY_URLS])];
        const events = await pool.querySync(
            relays,
            {
                kinds: [CUSTOM_REACTION_SET_KIND],
                authors: [publicKey],
                '#d': [CUSTOM_REACTION_SET_D_TAG],
                limit: 5
            },
            { maxWait: 9000 }
        );
        const newest = (events || []).sort((a, b) => (b.created_at || 0) - (a.created_at || 0))[0];
        const parsedSet = parseCustomReactionSetMeta(newest);
        customReactionEmojiSet = parsedSet.emojis;
        customReactionEmojiUrlMap = parsedSet.urlMap;
    } catch (e) {
        console.warn('Could not load custom reaction set from Nostr:', e);
        customReactionEmojiSet = [];
        customReactionEmojiUrlMap = {};
    }
}

async function saveOwnCustomReactionSetToNostr(list) {
    if (!pool || !publicKey) {
        throw new Error('Connect first.');
    }
    const emojis = normalizeCustomEmojiLines((list || []).join('\n'));
    const emojiTags = [];
    const publishedUrlMap = {};
    for (const token of emojis) {
        const shortcode = emojiShortcodeFromToken(token);
        if (!shortcode) continue;
        const url = customReactionEmojiUrlMap[shortcode];
        if (!url) continue;
        emojiTags.push(['emoji', shortcode, url]);
        publishedUrlMap[shortcode] = url;
    }
    if (!emojiTags.length) {
        throw new Error('No NIP-30 emoji tag entries available to publish.');
    }
    const ev = {
        kind: CUSTOM_REACTION_SET_KIND,
        created_at: Math.floor(Date.now() / 1000),
        tags: [
            ['d', CUSTOM_REACTION_SET_D_TAG],
            ['title', CUSTOM_REACTION_SET_D_TAG],
            ...emojiTags
        ],
        content: ''
    };
    const signed = await window.nostr.signEvent(ev);
    const targets = [...new Set([...(dmRelayUrls?.length ? dmRelayUrls : []), ...RELAY_URLS])];
    const publishAttempts = targets.map(async (url) => {
        await pool.publish([url], signed);
        return url;
    });
    await Promise.any(publishAttempts);
    customReactionEmojiSet = emojis;
    customReactionEmojiUrlMap = publishedUrlMap;
}

function setInboxLoading(loading) {
    isInboxLoading = Boolean(loading);
    const el = document.getElementById('inboxLoading');
    if (el) {
        el.hidden = !isInboxLoading;
    }
}

function buildSearchHit(pubkey, displayName = null, picture = null) {
    const pk = normalizePubkey(pubkey);
    let label = displayName;
    if (!label) {
        try {
            const n = nip19.npubEncode(pk);
            label = n.slice(0, 18) + (n.length > 18 ? '…' : '');
        } catch {
            label = pk.slice(0, 8) + '…' + pk.slice(-6);
        }
    }
    let npubDisplay = pk.slice(0, 14) + '…';
    try {
        npubDisplay = nip19.npubEncode(pk);
    } catch {
        /* keep short hex */
    }
    return { pubkey: pk, label, npubDisplay, picture };
}

async function throttleNostrWine() {
    const gap = 1050 - (Date.now() - lastNostrWineRequestMs);
    if (gap > 0) {
        await new Promise((r) => setTimeout(r, gap));
    }
    lastNostrWineRequestMs = Date.now();
}

/**
 * @param {string} query
 * @param {AbortSignal} signal
 * @returns {Promise<Array<{ pubkey: string, label: string, npubDisplay: string, picture: string | null }>>}
 */
async function fetchNostrUserSuggestions(query, signal) {
    const q = query.trim();
    if (!q) {
        return [];
    }

    if (/^[a-fA-F0-9]{64}$/.test(q)) {
        const pk = normalizePubkey(q);
        if (publicKey && pk === publicKey) {
            return [];
        }
        return [buildSearchHit(pk)];
    }

    if (q.startsWith('npub')) {
        try {
            const decoded = nip19.decode(q);
            if (decoded.type === 'npub') {
                const pk = normalizePubkey(decoded.data);
                if (publicKey && pk === publicKey) {
                    return [];
                }
                return [buildSearchHit(pk)];
            }
        } catch {
            return [];
        }
    }

    if (q.length < 2) {
        return [];
    }

    await throttleNostrWine();
    if (signal.aborted) {
        return [];
    }

    const url = `${NOSTR_WINE_SEARCH_URL}?${new URLSearchParams({ query: q, kind: '0', limit: '20' })}`;
    const res = await fetch(url, { signal, headers: { Accept: 'application/json' } });
    if (!res.ok) {
        throw new Error(`Search failed (${res.status})`);
    }
    const json = await res.json();
    const seen = new Set();
    const hits = [];

    for (const ev of json.data || []) {
        if (!ev || ev.kind !== 0 || !ev.pubkey) {
            continue;
        }
        const pk = normalizePubkey(ev.pubkey);
        if (publicKey && pk === publicKey) {
            continue;
        }
        if (seen.has(pk)) {
            continue;
        }
        seen.add(pk);

        let label = pk.slice(0, 8) + '…' + pk.slice(-6);
        let picture = null;
        try {
            const meta = JSON.parse(ev.content || '{}');
            label = meta.display_name || meta.displayName || meta.name || label;
            picture = typeof meta.picture === 'string' && meta.picture.length > 0 ? meta.picture : null;
        } catch {
            /* ignore */
        }
        hits.push(buildSearchHit(pk, label, picture));
        if (hits.length >= 16) {
            break;
        }
    }
    return hits;
}

function closeFabMenu() {
    const menu = document.getElementById('fabMenu');
    const btn = document.getElementById('fabPlusBtn');
    if (menu) {
        menu.hidden = true;
    }
    if (btn) {
        btn.setAttribute('aria-expanded', 'false');
    }
}

function toggleFabMenu() {
    const menu = document.getElementById('fabMenu');
    const btn = document.getElementById('fabPlusBtn');
    if (!menu || !btn) {
        return;
    }
    const willOpen = menu.hidden;
    menu.hidden = !willOpen;
    btn.setAttribute('aria-expanded', willOpen ? 'true' : 'false');
    if (willOpen) {
        const first = menu.querySelector('button');
        if (first) {
            first.focus();
        }
    }
}

function isOverlayOpen() {
    const modal = document.getElementById('newChatModal');
    const settings = document.getElementById('settingsModal');
    const lightbox = document.getElementById('imageLightbox');
    return Boolean((modal && !modal.hidden) || (settings && !settings.hidden) || (lightbox && !lightbox.hidden));
}

function syncBodyOverlayLock() {
    document.body.style.overflow = isOverlayOpen() ? 'hidden' : '';
}

function openNewChatModal() {
    const modal = document.getElementById('newChatModal');
    const input = document.getElementById('newChatSearch');
    const sugg = document.getElementById('newChatSuggestions');
    const status = document.getElementById('newChatSearchStatus');
    if (!modal || !input) {
        return;
    }
    closeFabMenu();
    wineSearchSerial += 1;
    wineSearchAbort?.abort();
    if (wineSearchDebounceTimer) {
        clearTimeout(wineSearchDebounceTimer);
    }
    modal.hidden = false;
    input.value = '';
    if (sugg) {
        sugg.innerHTML = '';
        sugg.hidden = true;
    }
    if (status) {
        status.textContent =
            'Type a name, paste a full npub, or enter a 64-character hex pubkey. Name search uses nostr.wine (about 1 lookup per second).';
    }
    syncBodyOverlayLock();
    setTimeout(() => input.focus(), 50);
}

function closeNewChatModal() {
    const modal = document.getElementById('newChatModal');
    if (modal) {
        modal.hidden = true;
    }
    syncBodyOverlayLock();
    wineSearchAbort?.abort();
    if (wineSearchDebounceTimer) {
        clearTimeout(wineSearchDebounceTimer);
    }
    wineSearchSerial += 1;
}

function normalizeRelayUrl(raw) {
    const t = (raw || '').trim();
    if (!t) return null;
    let u;
    try {
        u = new URL(t);
    } catch {
        return null;
    }
    if (u.protocol !== 'wss:') {
        return null;
    }
    u.hash = '';
    u.search = '';
    return u.toString().replace(/\/$/, '');
}

function renderSettingsRelayList() {
    const list = document.getElementById('settingsRelayList');
    if (!list) return;
    list.innerHTML = '';
    if (!settingsRelayDraft.length) {
        list.innerHTML = '<div class="new-chat-suggestion-empty" role="status">No DM relays configured yet.</div>';
        return;
    }
    for (const relay of settingsRelayDraft) {
        const row = document.createElement('div');
        row.className = 'settings-relay-item';
        const text = document.createElement('div');
        text.className = 'settings-relay-url';
        text.textContent = relay;
        text.title = relay;
        const rm = document.createElement('button');
        rm.type = 'button';
        rm.className = 'settings-relay-remove';
        rm.setAttribute('aria-label', `Remove relay ${relay}`);
        rm.textContent = '×';
        rm.addEventListener('click', () => {
            settingsRelayDraft = settingsRelayDraft.filter((r) => r !== relay);
            renderSettingsRelayList();
        });
        row.appendChild(text);
        row.appendChild(rm);
        list.appendChild(row);
    }
}

function currentEmojiEditorText() {
    const list = customReactionEmojiSet.length
        ? customReactionEmojiSet
        : [...DEFAULT_QUICK_REACTIONS, ...DEFAULT_EXTRA_REACTIONS];
    return list.join('\n');
}

function renderSettingsEmojiPreview(emojis) {
    const host = document.getElementById('settingsEmojiPreview');
    if (!host) return;
    host.innerHTML = '';
    if (!emojis.length) {
        host.innerHTML = '<div class="new-chat-suggestion-empty" role="status">No emojis to preview.</div>';
        return;
    }
    for (const token of emojis.slice(0, 64)) {
        const item = document.createElement('div');
        item.className = 'settings-emoji-preview-item';
        const shortcode = emojiShortcodeFromToken(token);
        const url = shortcode ? customReactionEmojiUrlMap[shortcode] : '';
        if (url) {
            const img = document.createElement('img');
            img.src = url;
            img.alt = token;
            img.referrerPolicy = 'no-referrer';
            img.loading = 'lazy';
            item.appendChild(img);
        } else {
            if (shortcode) {
                continue;
            }
            item.textContent = token;
        }
        host.appendChild(item);
    }
}

function createReactionOptionButton(emoji, picker, msg, onBeforeSend) {
    const b = document.createElement('button');
    b.type = 'button';
    b.className = 'message-reaction-option';
    const shortcode = emojiShortcodeFromToken(emoji);
    const url = shortcode ? customReactionEmojiUrlMap[shortcode] : '';
    if (url) {
        const img = document.createElement('img');
        img.src = url;
        img.alt = emoji;
        img.className = 'message-reaction-custom-emoji';
        img.referrerPolicy = 'no-referrer';
        img.loading = 'lazy';
        b.appendChild(img);
        b.title = emoji;
    } else {
        b.textContent = emoji;
    }
    b.addEventListener('click', (e) => {
        e.stopPropagation();
        picker.hidden = true;
        if (typeof onBeforeSend === 'function') onBeforeSend();
        void sendReactionToMessage(msg, emoji);
    });
    return b;
}

async function openSettingsModal() {
    const modal = document.getElementById('settingsModal');
    const input = document.getElementById('settingsRelayInput');
    const status = document.getElementById('settingsRelayStatus');
    const emojiStatus = document.getElementById('settingsEmojiStatus');
    const discoverStatus = document.getElementById('settingsEmojiDiscoverStatus');
    if (!modal || !publicKey) return;
    modal.hidden = false;
    syncBodyOverlayLock();
    await loadOwnCustomReactionSetFromNostr();
    settingsRelayDraft = await fetchKind10050Relays(publicKey);
    if (!settingsRelayDraft.length) {
        settingsRelayDraft = [...RELAY_URLS];
    }
    renderSettingsRelayList();
    if (status) {
        status.textContent = 'Edit your DM inbox relays and save to publish kind 10050.';
    }
    if (input) {
        input.value = 'wss://';
        setTimeout(() => input.focus(), 30);
    }
    settingsEmojiDraftSet = customReactionEmojiSet.length
        ? [...customReactionEmojiSet]
        : [...DEFAULT_QUICK_REACTIONS, ...DEFAULT_EXTRA_REACTIONS];
    renderSettingsEmojiPreview(settingsEmojiDraftSet);
    if (emojiStatus) {
        emojiStatus.textContent = customReactionEmojiSet.length
            ? `Loaded ${customReactionEmojiSet.length} custom emojis from Nostr.`
            : 'No custom set on Nostr. Using default emoji set.';
    }
    if (discoverStatus) {
        discoverStatus.textContent = 'Click refresh to discover public sets.';
    }
    discoveredEmojiSets = [];
    renderDiscoveredEmojiSets();
}

function closeSettingsModal() {
    const modal = document.getElementById('settingsModal');
    if (modal) modal.hidden = true;
    syncBodyOverlayLock();
}

async function saveSettingsRelays() {
    const status = document.getElementById('settingsRelayStatus');
    const saveBtn = document.getElementById('settingsSaveBtn');
    if (!pool || !publicKey) {
        if (status) status.textContent = 'Connect first.';
        return;
    }
    if (!settingsRelayDraft.length) {
        if (status) status.textContent = 'Add at least one relay URL.';
        return;
    }
    if (saveBtn) saveBtn.disabled = true;
    if (status) status.textContent = 'Saving…';
    try {
        const ev = {
            kind: 10050,
            created_at: Math.floor(Date.now() / 1000),
            tags: settingsRelayDraft.map((url) => ['relay', url]),
            content: ''
        };
        const signed = await window.nostr.signEvent(ev);
        const targets = [...new Set([...dmRelayUrls, ...RELAY_URLS, ...settingsRelayDraft])];
        const publishAttempts = targets.map(async (url) => {
            await pool.publish([url], signed);
            return url;
        });
        await Promise.any(publishAttempts);
        dmRelayUrls = [...new Set(settingsRelayDraft)];
        if (status) status.textContent = `Saved ${settingsRelayDraft.length} relay(s).`;
    } catch (err) {
        if (status) status.textContent = 'Could not publish settings. Try again.';
        console.error('Failed to save kind 10050 relays:', err);
    } finally {
        if (saveBtn) saveBtn.disabled = false;
    }
}

function initSettingsUi() {
    const btn = document.getElementById('sidebarSettingsBtn');
    const modal = document.getElementById('settingsModal');
    const close = document.getElementById('settingsModalClose');
    const addBtn = document.getElementById('settingsRelayAddBtn');
    const input = document.getElementById('settingsRelayInput');
    const saveBtn = document.getElementById('settingsSaveBtn');
    const status = document.getElementById('settingsRelayStatus');
    const emojiSaveBtn = document.getElementById('settingsEmojiSaveBtn');
    const emojiResetBtn = document.getElementById('settingsEmojiResetBtn');
    const emojiStatus = document.getElementById('settingsEmojiStatus');
    const emojiDiscoverBtn = document.getElementById('settingsEmojiDiscoverBtn');

    if (btn) {
        btn.addEventListener('click', () => {
            void openSettingsModal();
        });
    }
    if (modal) {
        modal.addEventListener('click', (e) => {
            if (e.target === modal) closeSettingsModal();
        });
    }
    if (close) {
        close.addEventListener('click', closeSettingsModal);
    }
    if (addBtn && input) {
        addBtn.addEventListener('click', () => {
            const normalized = normalizeRelayUrl(input.value);
            if (!normalized) {
                if (status) status.textContent = 'Enter a valid wss:// relay URL.';
                return;
            }
            if (!settingsRelayDraft.includes(normalized)) {
                settingsRelayDraft.push(normalized);
                settingsRelayDraft = [...new Set(settingsRelayDraft)];
                renderSettingsRelayList();
                if (status) status.textContent = '';
            }
            input.value = 'wss://';
            input.focus();
        });
        input.addEventListener('keydown', (e) => {
            if (e.key === 'Enter') {
                e.preventDefault();
                addBtn.click();
            }
        });
    }
    if (saveBtn) {
        saveBtn.addEventListener('click', () => {
            void saveSettingsRelays();
        });
    }
    if (emojiSaveBtn) {
        emojiSaveBtn.addEventListener('click', async () => {
            const parsed = normalizeCustomEmojiLines(settingsEmojiDraftSet.join('\n'));
            if (parsed.length < 5) {
                if (emojiStatus) emojiStatus.textContent = 'Import a set with at least 5 emojis.';
                return;
            }
            emojiSaveBtn.disabled = true;
            if (emojiStatus) emojiStatus.textContent = 'Saving to Nostr…';
            try {
                await saveOwnCustomReactionSetToNostr(parsed);
                if (emojiStatus) emojiStatus.textContent = `Saved ${customReactionEmojiSet.length} custom emojis to Nostr.`;
                settingsEmojiDraftSet = [...customReactionEmojiSet];
                renderSettingsEmojiPreview(settingsEmojiDraftSet);
                if (currentChat) {
                    displayMessages(currentChat);
                }
            } catch (e) {
                if (emojiStatus) emojiStatus.textContent = 'Could not save emoji set to Nostr.';
            } finally {
                emojiSaveBtn.disabled = false;
            }
        });
    }
    if (emojiResetBtn) {
        emojiResetBtn.addEventListener('click', async () => {
            emojiResetBtn.disabled = true;
            if (emojiStatus) emojiStatus.textContent = 'Resetting on Nostr…';
            try {
                await saveOwnCustomReactionSetToNostr([]);
            } catch (e) {
                if (emojiStatus) emojiStatus.textContent = 'Could not reset emoji set on Nostr.';
                emojiResetBtn.disabled = false;
                return;
            }
            settingsEmojiDraftSet = [...DEFAULT_QUICK_REACTIONS, ...DEFAULT_EXTRA_REACTIONS];
            renderSettingsEmojiPreview(settingsEmojiDraftSet);
            if (emojiStatus) emojiStatus.textContent = 'Reset to default emoji set (saved on Nostr).';
            if (currentChat) {
                displayMessages(currentChat);
            }
            emojiResetBtn.disabled = false;
        });
    }
    if (emojiDiscoverBtn) {
        emojiDiscoverBtn.addEventListener('click', () => {
            void discoverEmojiSets();
        });
    }
}

function openImageLightbox(src) {
    if (!src) return;
    const lightbox = document.getElementById('imageLightbox');
    const img = document.getElementById('imageLightboxImg');
    if (!lightbox || !img) return;
    img.src = src;
    lightbox.hidden = false;
    syncBodyOverlayLock();
}

function closeImageLightbox() {
    const lightbox = document.getElementById('imageLightbox');
    const img = document.getElementById('imageLightboxImg');
    if (!lightbox || !img) return;
    lightbox.hidden = true;
    img.removeAttribute('src');
    syncBodyOverlayLock();
}

function initImageLightbox() {
    const lightbox = document.getElementById('imageLightbox');
    const closeBtn = document.getElementById('imageLightboxClose');
    if (!lightbox) return;

    if (closeBtn) {
        closeBtn.addEventListener('click', closeImageLightbox);
    }

    lightbox.addEventListener('click', (e) => {
        if (e.target === lightbox) {
            closeImageLightbox();
        }
    });

    document.addEventListener('click', (e) => {
        const target = e.target;
        if (!(target instanceof HTMLElement)) return;
        const img = target.closest('.message-inline-image');
        if (!(img instanceof HTMLImageElement)) return;
        if (!img.src) return;
        e.preventDefault();
        openImageLightbox(img.src);
    });
}

function scheduleNewChatSearch(raw) {
    wineSearchAbort?.abort();
    const serial = ++wineSearchSerial;
    const statusEl = document.getElementById('newChatSearchStatus');
    const suggEl = document.getElementById('newChatSuggestions');

    if (wineSearchDebounceTimer) {
        clearTimeout(wineSearchDebounceTimer);
    }

    wineSearchDebounceTimer = setTimeout(async () => {
        wineSearchAbort = new AbortController();
        const { signal } = wineSearchAbort;
        const q = raw.trim();

        try {
            if (q.length === 0) {
                if (statusEl) {
                    statusEl.textContent =
                        'Type a name, paste a full npub, or enter a 64-character hex pubkey. Name search uses nostr.wine (about 1 lookup per second).';
                }
                if (suggEl) {
                    suggEl.innerHTML = '';
                    suggEl.hidden = true;
                }
                return;
            }

            if (q.length < 2 && !/^[a-fA-F0-9]{64}$/.test(q) && !q.startsWith('npub')) {
                if (statusEl) {
                    statusEl.textContent = 'Type at least 2 characters to search by name, or paste an npub / hex key.';
                }
                if (suggEl) {
                    suggEl.innerHTML = '';
                    suggEl.hidden = true;
                }
                return;
            }

            if (statusEl) {
                statusEl.textContent = 'Searching…';
            }

            const hits = await fetchNostrUserSuggestions(q, signal);
            if (serial !== wineSearchSerial) {
                return;
            }
            if (statusEl) {
                statusEl.textContent = hits.length ? `${hits.length} result(s)` : 'No matches.';
            }
            renderNewChatSuggestions(hits);
        } catch (e) {
            if (e?.name === 'AbortError') {
                return;
            }
            if (serial !== wineSearchSerial) {
                return;
            }
            console.warn('Nostr search failed:', e);
            if (statusEl) {
                statusEl.textContent = 'Search failed. Wait a second and try again (rate limit), or check your connection.';
            }
            if (suggEl) {
                suggEl.innerHTML =
                    '<div class="new-chat-suggestion-empty" role="status">Could not load suggestions.</div>';
                suggEl.hidden = false;
            }
        }
    }, 420);
}

function renderNewChatSuggestions(hits) {
    const root = document.getElementById('newChatSuggestions');
    if (!root) {
        return;
    }
    root.innerHTML = '';

    if (!hits.length) {
        root.innerHTML = '<div class="new-chat-suggestion-empty" role="status">No matches. Try another name or paste an npub.</div>';
        root.hidden = false;
        return;
    }

    for (const hit of hits) {
        const row = document.createElement('button');
        row.type = 'button';
        row.className = 'new-chat-suggestion';
        row.setAttribute('role', 'option');

        let avEl;
        if (hit.picture) {
            const img = document.createElement('img');
            img.className = 'new-chat-suggestion-avatar';
            img.src = hit.picture;
            img.alt = '';
            img.loading = 'lazy';
            img.referrerPolicy = 'no-referrer';
            img.addEventListener('error', () => {
                img.replaceWith(makeAvatarPlaceholder(hit));
            });
            avEl = img;
        } else {
            avEl = makeAvatarPlaceholder(hit);
        }

        const text = document.createElement('div');
        text.className = 'new-chat-suggestion-text';
        const nameEl = document.createElement('div');
        nameEl.className = 'new-chat-suggestion-name';
        nameEl.textContent = hit.label;
        const npubEl = document.createElement('div');
        npubEl.className = 'new-chat-suggestion-npub';
        npubEl.textContent = hit.npubDisplay;
        text.appendChild(nameEl);
        text.appendChild(npubEl);

        row.appendChild(avEl);
        row.appendChild(text);

        row.addEventListener('click', () => {
            void beginChatWithPubkey(hit.pubkey, hit);
        });
        root.appendChild(row);
    }
    root.hidden = false;
}

function makeAvatarPlaceholder(hit) {
    const el = document.createElement('div');
    el.className = 'new-chat-suggestion-avatar';
    el.style.display = 'flex';
    el.style.alignItems = 'center';
    el.style.justifyContent = 'center';
    el.style.fontSize = '13px';
    el.style.fontWeight = '600';
    el.style.color = '#888';
    el.textContent = (hit.label || '?').trim().slice(0, 1).toUpperCase();
    return el;
}

async function beginChatWithPubkey(hex, hit = null) {
    const pk = normalizePubkey(hex);
    if (publicKey && pk === publicKey) {
        alert('You cannot start a chat with yourself.');
        return;
    }

    try {
        if (!conversations[pk]) {
            conversations[pk] = [];
        }
        if (hit) {
            userProfiles[pk] = {
                name: hit.label,
                display_name: hit.label,
                picture: hit.picture,
                about: userProfiles[pk]?.about ?? null,
            };
        }
        await fetchUserProfile(pk);
        closeNewChatModal();
        closeFabMenu();
        openChat(pk);
    } catch (error) {
        alert('Could not open chat: ' + (error?.message || String(error)));
    }
}

function initNewChatUi() {
    const fabBtn = document.getElementById('fabPlusBtn');
    const fabMenu = document.getElementById('fabMenu');
    const fabNewChat = document.getElementById('fabMenuNewChat');
    const modal = document.getElementById('newChatModal');
    const modalClose = document.getElementById('newChatModalClose');
    const searchInput = document.getElementById('newChatSearch');

    if (fabBtn && fabMenu) {
        fabBtn.addEventListener('click', (e) => {
            e.stopPropagation();
            toggleFabMenu();
        });
    }

    if (fabNewChat) {
        fabNewChat.addEventListener('click', () => {
            openNewChatModal();
        });
    }

    document.addEventListener('click', (e) => {
        if (!fabMenu || fabMenu.hidden) {
            return;
        }
        const t = e.target;
        if (fabBtn?.contains(t) || fabMenu.contains(t)) {
            return;
        }
        closeFabMenu();
    });

    if (modal) {
        modal.addEventListener('click', (e) => {
            if (e.target === modal) {
                closeNewChatModal();
            }
        });
    }
    if (modalClose) {
        modalClose.addEventListener('click', () => closeNewChatModal());
    }

    if (searchInput) {
        searchInput.addEventListener('input', () => {
            scheduleNewChatSearch(searchInput.value);
        });
    }

    document.addEventListener('keydown', (e) => {
        if (e.key !== 'Escape') {
            return;
        }
        const lightbox = document.getElementById('imageLightbox');
        if (lightbox && !lightbox.hidden) {
            closeImageLightbox();
            e.preventDefault();
            return;
        }
        const modalEl = document.getElementById('newChatModal');
        if (modalEl && !modalEl.hidden) {
            closeNewChatModal();
            e.preventDefault();
            return;
        }
        const settingsEl = document.getElementById('settingsModal');
        if (settingsEl && !settingsEl.hidden) {
            closeSettingsModal();
            e.preventDefault();
            return;
        }
        closeFabMenu();
    });
}

/** Grapheme-safe emoji list for the in-app picker (Array.from preserves surrogate pairs). */
const EMOJI_PICKER_CHARS = Array.from(
    '😀😃😄😁😅😂🤣🥲😊😇🙂😉😌😍🥰😘😗😙😚😋😛😜🤪🤑🤗🤭🤔🤐🤨😐😑😏😒🙄😬🤥😪🤤😴🥱😮😯😲😳🥺😦😧😨😰😥😢😭😱😖😣😞😓😩😫🤯🤠🥳🥸😎🤓🧐😕😟🙁☹️😡🤬😈👿🤡💀☠️💩👻👽👾🤖💋💘💝💖💗💓💞💕💟❣️💔❤️🧡💛💚💙💜🤎🖤🤍💯💢💥💫💦💨👋🤚🖐️✋🖖👌🤌✌️🤞🤟🤘🤙👍👎✊👏🙌👐🤲🤝🙏✍️💪🦾🫶👀👂🦻👃🧠💬🗨️👁️💤🔥✨⭐🌟💫⚡🎉🎊✅❌❓❗📌📎🔗🧵🍻☕🫖🎯🏆🎮'
);

function insertAtCursor(textarea, text) {
    if (!textarea || typeof text !== 'string') return;
    textarea.focus();
    const start = textarea.selectionStart ?? 0;
    const end = textarea.selectionEnd ?? 0;
    if (typeof textarea.setRangeText === 'function') {
        textarea.setRangeText(text, start, end, 'end');
    } else {
        const value = textarea.value;
        textarea.value = value.slice(0, start) + text + value.slice(end);
        const pos = start + text.length;
        textarea.selectionStart = textarea.selectionEnd = pos;
    }
    textarea.dispatchEvent(new Event('input', { bubbles: true }));
}

function initEmojiPicker() {
    const panel = document.getElementById('emojiPanel');
    const btn = document.getElementById('emojiToggleBtn');
    const input = document.getElementById('messageInput');
    if (!panel || !btn || !input) return;

    const grid = document.createElement('div');
    grid.className = 'emoji-grid';
    for (const ch of EMOJI_PICKER_CHARS) {
        const cell = document.createElement('button');
        cell.type = 'button';
        cell.className = 'emoji-cell';
        cell.textContent = ch;
        cell.title = ch;
        cell.addEventListener('click', () => {
            insertAtCursor(input, ch);
        });
        grid.appendChild(cell);
    }
    panel.appendChild(grid);

    function closePanel() {
        panel.hidden = true;
        btn.setAttribute('aria-expanded', 'false');
    }

    function openPanel() {
        panel.hidden = false;
        btn.setAttribute('aria-expanded', 'true');
    }

    btn.addEventListener('click', (e) => {
        e.stopPropagation();
        if (panel.hidden) openPanel();
        else closePanel();
    });

    document.addEventListener('click', (e) => {
        if (panel.hidden) return;
        const t = e.target;
        if (panel.contains(t) || btn.contains(t)) return;
        closePanel();
    });

    document.addEventListener('keydown', (e) => {
        if (e.key === 'Escape' && !panel.hidden) {
            closePanel();
            btn.focus();
        }
    });
}

/** Lowercase hex pubkey for stable Map keys and comparisons */
function normalizePubkey(pk) {
    if (typeof pk !== 'string' || !/^[a-fA-F0-9]{64}$/.test(pk)) return pk;
    return pk.toLowerCase();
}

// Check if NIP-07 extension is available
function hasNostrExtension() {
    return typeof window.nostr !== 'undefined';
}

async function connectWithExtension() {
    if (!hasNostrExtension()) {
        alert('No Nostr extension detected!\n\nPlease install a NIP-07 compatible extension:\n\n• Alby (recommended) — https://getalby.com/\n• nos2x — https://github.com/fiatjaf/nos2x\n• Flamingo — https://getflamingo.org/\n• horse — https://github.com/fiatjaf/horse\n\nAfter installing, refresh this page and try again.');
        return;
    }

    try {
        // Get public key from extension (normalize so tag/filter comparisons match)
        publicKey = normalizePubkey(await window.nostr.getPublicKey());

        // Check if extension supports NIP-44 (required for this app)
        if (!window.nostr.nip44 || !window.nostr.nip44.encrypt || !window.nostr.nip44.decrypt) {
            alert('Your Nostr extension does not support NIP-44 encryption/decryption.\n\n' +
                  'This app requires NIP-44 support for secure messaging.\n\n' +
                  'Please use an extension that supports NIP-44:\n' +
                  '• Alby (recommended) — https://getalby.com/\n' +
                  '• Or another extension with NIP-44 support\n\n' +
                  'After installing/updating, refresh this page.');
            return;
        }

        if (messageSubscription) {
            try {
                messageSubscription.close();
            } catch (e) {
                console.warn('Closing previous message subscription:', e);
            }
            messageSubscription = null;
        }
        if (pool) {
            stopIncrementalInboxSync();
            gapFillDebounceByConv.forEach((t) => clearTimeout(t));
            gapFillDebounceByConv.clear();
            gapFillLastRunMs.clear();
            conversationRepairRunning.clear();
            try {
                pool.destroy();
            } catch (e) {
                console.warn('Destroying previous relay pool:', e);
            }
        }
        lastInboxGiftWrapProcessedSec = 0;
        pool = new SimplePool();
        
        // Bootstrap against defaults so we can discover our kind 10050 relay list.
        document.getElementById('statusText').textContent = 'Connecting to relays...';
        const bootstrapResults = await connectRelaySet(RELAY_URLS);
        const ownInboxRelays = await fetchKind10050Relays(publicKey);
        dmRelayUrls = ownInboxRelays.length ? [...new Set(ownInboxRelays)] : [...RELAY_URLS];
        const additionalRelayUrls = dmRelayUrls.filter((url) => !RELAY_URLS.includes(url));
        const additionalResults = additionalRelayUrls.length ? await connectRelaySet(additionalRelayUrls) : [];
        const relayResults = [...bootstrapResults, ...additionalResults];
        const successfulConnections = relayResults.filter((r) => r.success).length;
        const totalConnectedTargets = [...new Set([...RELAY_URLS, ...additionalRelayUrls])].length;
        const relayStatusByUrl = new Map(relayResults.map((r) => [r.url, r]));
        const inboxRelayStatuses = ownInboxRelays.length
            ? dmRelayUrls.map((url) => relayStatusByUrl.get(url) || { url, success: false })
            : [];

        document.getElementById('statusDot').classList.add('connected');
        document.getElementById('statusText').textContent = ownInboxRelays.length
            ? `Connected to ${successfulConnections}/${totalConnectedTargets} relays`
            : `Connected to ${successfulConnections}/${RELAY_URLS.length} relays`;
        document.getElementById('connectionSetup').style.display = 'none';
        document.body.classList.add('is-authenticated');
        const fab = document.getElementById('sidebarFab');
        if (fab) {
            fab.removeAttribute('hidden');
        }
        const settingsBtn = document.getElementById('sidebarSettingsBtn');
        if (settingsBtn) {
            settingsBtn.removeAttribute('hidden');
        }
        const chatAreaEl = document.getElementById('chatArea');
        if (chatAreaEl) chatAreaEl.removeAttribute('hidden');
        setInboxLoading(true);

        setRelayStatusTooltip(bootstrapResults, inboxRelayStatuses);
        await loadOwnCustomReactionSetFromNostr();

        // Live subscription first so new mail arrives while history is still decrypting.
        // History uses paginated querySync (relay result caps) + batched UI updates for mobile perf.
        subscribeToMessages();
        startIncrementalInboxSync();
        void fetchHistoricalGiftWraps().finally(() => {
            setInboxLoading(false);
        });

    } catch (error) {
        setInboxLoading(false);
        alert('Connection failed: ' + error.message);
        console.error(error);
    }
}

// Fetch user profile (kind 0) to get display name
async function fetchUserProfile(pubkey) {
    if (userProfiles[pubkey]) {
        return userProfiles[pubkey]; // Already cached
    }

    try {
        // Subscribe to kind 0 events for this user
        // Note: pool.subscribe takes a single filter object, not an array
        return new Promise((resolve) => {
            const sub = pool.subscribe(RELAY_URLS, {
                kinds: [0],
                authors: [pubkey],
                limit: 1
            }, {
                onevent(event) {
                    try {
                        const profile = JSON.parse(event.content);
                        userProfiles[pubkey] = {
                            name: profile.name || profile.display_name || null,
                            display_name: profile.display_name || profile.name || null,
                            picture: profile.picture || null,
                            about: profile.about || null
                        };
                        sub.close();
                        resolve(userProfiles[pubkey]);
                    } catch (err) {
                        console.error('Failed to parse profile', err);
                    }
                },
                oneose() {
                    // If no events found, set default
                    if (!userProfiles[pubkey]) {
                        userProfiles[pubkey] = { name: null, display_name: null, picture: null, about: null };
                    }
                    resolve(userProfiles[pubkey]);
                }
            });

            // Timeout after 3 seconds
            setTimeout(() => {
                if (!userProfiles[pubkey]) {
                    userProfiles[pubkey] = { name: null, display_name: null, picture: null, about: null };
                    sub.close();
                    resolve(userProfiles[pubkey]);
                }
            }, 3000);
        });
    } catch (error) {
        console.error('Failed to fetch profile for', pubkey, error);
        userProfiles[pubkey] = { name: null, display_name: null, picture: null, about: null };
        return userProfiles[pubkey];
    }
}

// Get display name for a pubkey (with fallback to short pubkey)
function getDisplayName(pubkey) {
    const profile = userProfiles[pubkey];
    if (profile && (profile.display_name || profile.name)) {
        return profile.display_name || profile.name;
    }
    // Fallback to short pubkey
    return pubkey.slice(0, 8) + '...' + pubkey.slice(-8);
}

/** Kind 10050: preferred relays to receive NIP-17 gift wraps (NIP-17 publishing + our subscription) */
async function fetchKind10050Relays(authorPubkey, options = {}) {
    try {
        const queryRelays = options.relays?.length
            ? [...new Set(options.relays)]
            : [...new Set([...(dmRelayUrls?.length ? dmRelayUrls : []), ...RELAY_URLS])];
        if (options.ensureConnections) {
            await connectRelaySet(queryRelays);
        }
        const events = await pool.querySync(
            queryRelays,
            { kinds: [10050], authors: [authorPubkey], limit: 8 },
            { maxWait: options.maxWait ?? 9000 }
        );
        const ev = (events || []).sort((a, b) => (b.created_at || 0) - (a.created_at || 0))[0];
        if (!ev?.tags?.length) return [];
        return ev.tags.filter((t) => t[0] === 'relay' && typeof t[1] === 'string' && t[1].length > 0).map((t) => t[1]);
    } catch (e) {
        console.warn('fetchKind10050Relays failed:', e);
        return [];
    }
}

/** Read from both default + discovered inbox relays to reduce missed events on flaky/mobile sockets. */
function getReadRelayUrls() {
    return [...new Set([...(dmRelayUrls || []), ...RELAY_URLS])];
}

function noteInboxGiftWrapProcessed(createdAt) {
    const t = typeof createdAt === 'number' && createdAt > 0 ? createdAt : 0;
    if (t > lastInboxGiftWrapProcessedSec) {
        lastInboxGiftWrapProcessedSec = t;
    }
}

/**
 * Page kind-1059 inbox queries backward in time (until cursor) so we are not limited to one relay page.
 * @param {string[]} readRelays
 * @param {(until?: number) => object} buildFilter — return filter without `limit`
 * @param {{ pageLimit: number, maxPages: number, maxWaitBase: number, suppressUi?: boolean }} opts
 */
async function ingestPagedGiftWraps(readRelays, buildFilter, opts) {
    const { pageLimit, maxPages, maxWaitBase, suppressUi = true } = opts;
    let until;
    for (let page = 0; page < maxPages; page++) {
        const filter = buildFilter(until);
        filter.limit = pageLimit;
        const maxWait = Math.min(65000, maxWaitBase + readRelays.length * 3500);
        const events = await pool.querySync(readRelays, filter, { maxWait });
        if (!events?.length) {
            break;
        }
        events.sort((a, b) => a.created_at - b.created_at);
        for (const ev of events) {
            try {
                await handleGiftWrappedMessage(ev, { suppressUi });
            } catch (err) {
                console.warn('ingestPagedGiftWraps: handle error:', err);
            }
        }
        if (events.length < pageLimit) {
            break;
        }
        until = events[0].created_at - 1;
    }
}

function stopIncrementalInboxSync() {
    if (incrementalInboxTimerId) {
        clearInterval(incrementalInboxTimerId);
        incrementalInboxTimerId = null;
    }
}

function startIncrementalInboxSync() {
    stopIncrementalInboxSync();
    incrementalInboxTimerId = setInterval(() => {
        void runIncrementalInboxSync();
    }, INCREMENTAL_INBOX_INTERVAL_MS);
}

async function runIncrementalInboxSync() {
    if (!pool || !publicKey || incrementalInboxInFlight) {
        return;
    }
    incrementalInboxInFlight = true;
    try {
        const readRelays = getReadRelayUrls();
        const nowSec = Math.floor(Date.now() / 1000);
        const baseline = lastInboxGiftWrapProcessedSec > 0 ? lastInboxGiftWrapProcessedSec : nowSec - 24 * 60 * 60;
        const since = Math.max(0, baseline - INCREMENTAL_INBOX_OVERLAP_SECS);
        await ingestPagedGiftWraps(
            readRelays,
            (until) => {
                const f = { kinds: [1059], '#p': [publicKey], since };
                if (until !== undefined) {
                    f.until = until;
                }
                return f;
            },
            {
                pageLimit: INCREMENTAL_INBOX_PAGE_LIMIT,
                maxPages: INCREMENTAL_INBOX_MAX_PAGES,
                maxWaitBase: 9000,
                suppressUi: true
            }
        );
        updateConversationsList();
        if (currentChat) {
            queueActiveChatRender(currentChat, { header: true });
        }
    } catch (err) {
        console.warn('Incremental inbox sync failed:', err);
    } finally {
        incrementalInboxInFlight = false;
    }
}

function conversationHasPendingReactions(conversationPubkey) {
    const pk = normalizePubkey(conversationPubkey);
    for (const [, list] of pendingReactionsByMessageId) {
        if (!Array.isArray(list)) {
            continue;
        }
        if (list.some((p) => p && normalizePubkey(p.conversationPubkey) === pk)) {
            return true;
        }
    }
    return false;
}

function scheduleGapFillForConversation(conversationPubkey) {
    const pk = normalizePubkey(conversationPubkey);
    const prev = gapFillDebounceByConv.get(pk);
    if (prev) {
        clearTimeout(prev);
    }
    gapFillDebounceByConv.set(
        pk,
        setTimeout(() => {
            gapFillDebounceByConv.delete(pk);
            void runGapFillForConversation(pk);
        }, GAP_FILL_DEBOUNCE_MS)
    );
}

async function runGapFillForConversation(conversationPubkey) {
    if (!pool || !publicKey || !conversationPubkey) {
        return;
    }
    const pk = normalizePubkey(conversationPubkey);
    if (!conversationHasPendingReactions(pk)) {
        return;
    }
    const now = Date.now();
    if (now - (gapFillLastRunMs.get(pk) || 0) < GAP_FILL_COOLDOWN_MS) {
        return;
    }
    gapFillLastRunMs.set(pk, now);

    const readRelays = getReadRelayUrls();
    const since = Math.floor(Date.now() / 1000) - CONVERSATION_REPAIR_LOOKBACK_SECS;
    try {
        await ingestPagedGiftWraps(
            readRelays,
            (until) => {
                const f = { kinds: [1059], '#p': [publicKey], since };
                if (until !== undefined) {
                    f.until = until;
                }
                return f;
            },
            {
                pageLimit: CONVERSATION_REPAIR_LIMIT,
                maxPages: GAP_FILL_MAX_PAGES,
                maxWaitBase: 14000,
                suppressUi: true
            }
        );
    } catch (err) {
        console.warn('Gap-fill gift wrap ingest failed:', err);
    }

    updateConversationsList();
    if (currentChat === pk) {
        displayMessages(pk);
        updateChatHeader(pk);
    }
}

/** Connects the pool to the exact relay set and returns statuses. */
async function connectRelaySet(relays) {
    const statuses = await Promise.all(
        relays.map(async (url) => {
            try {
                await pool.ensureRelay(url);
                return { url, success: true };
            } catch (err) {
                console.warn('Failed to connect to relay:', url, err);
                return { url, success: false };
            }
        })
    );
    return statuses;
}

function setRelayStatusTooltip(defaultResults, inboxResults = []) {
    const indicator = document.getElementById('statusIndicator');
    const popover = document.getElementById('statusRelayPopover');
    if (!indicator || !popover) return;

    const lines = ['Default relays:'];
    for (const { url, success } of defaultResults) {
        lines.push(`${success ? '✓' : '✗'} ${url}`);
    }
    if (inboxResults.length > 0) {
        lines.push('');
        lines.push('Inbox relays (kind 10050):');
        for (const { url, success } of inboxResults) {
            lines.push(`${success ? '✓' : '✗'} ${url}`);
        }
    }

    popover.textContent = lines.join('\n');
    indicator.setAttribute('aria-describedby', 'statusRelayPopover');
    indicator.removeAttribute('title');
    indicator.tabIndex = 0;
}

// Generate random timestamp within 2 days in the past
function getRandomPastTimestamp() {
    const now = Math.floor(Date.now() / 1000);
    const twoDaysAgo = now - (2 * 24 * 60 * 60);
    return twoDaysAgo + Math.floor(Math.random() * (2 * 24 * 60 * 60));
}

/** Pull stored kind 1059 from relays (paginated: many relays cap events per REQ). */
async function fetchHistoricalGiftWraps() {
    if (!pool || !publicKey) return;

    const readRelays = getReadRelayUrls();
    const pageLimit = 500;
    const maxPages = 40;
    const maxWait = Math.min(65000, 20000 + readRelays.length * 6000);
    let until;

    try {
        for (let page = 0; page < maxPages; page++) {
            const filter = {
                kinds: [1059],
                '#p': [publicKey],
                limit: pageLimit
            };
            if (until !== undefined) {
                filter.until = until;
            }

            const events = await pool.querySync(readRelays, filter, { maxWait });
            if (!events.length) {
                break;
            }

            events.sort((a, b) => a.created_at - b.created_at);
            const oldest = events[0].created_at;

            for (const ev of events) {
                try {
                    await handleGiftWrappedMessage(ev, { suppressUi: true });
                } catch (err) {
                    console.error('Error handling historical gift wrap:', err);
                }
            }

            if (events.length < pageLimit) {
                break;
            }
            until = oldest - 1;
        }
    } catch (err) {
        console.warn('Historical gift wrap querySync failed:', err);
    }

    updateConversationsList();
    if (currentChat) {
        displayMessages(currentChat);
        updateChatHeader(currentChat);
    }
    prefetchMissingConversationProfiles();
}

/**
 * Repair fetch when opening a thread: paginated kind-1059 backfill so we are not limited to one relay response page.
 * @param {{ deep?: boolean }} [options] — deep: more pages / larger page size (from openChat on mobile-heavy paths)
 */
async function fetchConversationRepair(conversationPubkey, options = {}) {
    if (!pool || !publicKey || !conversationPubkey) {
        return;
    }
    const pk = normalizePubkey(conversationPubkey);
    if (conversationRepairRunning.has(pk)) {
        return;
    }

    const now = Date.now();
    const last = conversationRepairLastRunMs.get(pk) || 0;
    if (now - last < CONVERSATION_REPAIR_COOLDOWN_MS) {
        return;
    }
    conversationRepairLastRunMs.set(pk, now);
    conversationRepairRunning.add(pk);

    try {
        const readRelays = getReadRelayUrls();
        const since = Math.floor(Date.now() / 1000) - CONVERSATION_REPAIR_LOOKBACK_SECS;
        const pageLimit = options.deep ? REPAIR_PAGE_LIMIT_DEEP : CONVERSATION_REPAIR_LIMIT;
        const maxPages = options.deep ? REPAIR_MAX_PAGES_DEEP : REPAIR_MAX_PAGES_DEFAULT;
        await ingestPagedGiftWraps(
            readRelays,
            (until) => {
                const f = { kinds: [1059], '#p': [publicKey], since };
                if (until !== undefined) {
                    f.until = until;
                }
                return f;
            },
            { pageLimit, maxPages, maxWaitBase: 12000, suppressUi: true }
        );
    } catch (err) {
        console.warn('Conversation repair query failed:', err);
    } finally {
        conversationRepairRunning.delete(pk);
    }

    updateConversationsList();
    if (currentChat === pk) {
        displayMessages(pk);
        updateChatHeader(pk);
    }
}

/** After bulk inbox load, fetch display names without blocking decrypt. */
function prefetchMissingConversationProfiles() {
    for (const pubkey of Object.keys(conversations)) {
        if (userProfiles[pubkey]) {
            continue;
        }
        void fetchUserProfile(pubkey).then(() => {
            queueConversationsListUpdate();
            queueChatHeaderUpdate(pubkey);
        });
    }
}

function getRumorConversationPubkey(rumor, authorPubkey) {
    let conversationPubkey = authorPubkey;
    if (authorPubkey === publicKey) {
        const pTag = Array.isArray(rumor.tags)
            ? rumor.tags.find((t) => t[0] === 'p' && typeof t[1] === 'string' && t[1].length)
            : null;
        if (!pTag) {
            return null;
        }
        conversationPubkey = normalizePubkey(pTag[1]);
    }
    return conversationPubkey;
}

/** First tag value for name (NIP-17 file tags, etc.). */
function rumorTagValue(tags, name) {
    if (!Array.isArray(tags)) return '';
    const row = tags.find((t) => t[0] === name && typeof t[1] === 'string' && t[1].length);
    return row ? row[1] : '';
}

/** NIP-17 kind 15 file message — content is file URL; tags carry crypto metadata. */
function parseKind15FileMeta(rumor) {
    const url = typeof rumor.content === 'string' ? rumor.content.trim() : '';
    if (!url) return null;
    const tags = rumor.tags;
    return {
        fileType: rumorTagValue(tags, 'file-type') || 'application/octet-stream',
        url,
        encryptionAlgorithm: rumorTagValue(tags, 'encryption-algorithm'),
        decryptionKey: rumorTagValue(tags, 'decryption-key'),
        decryptionNonce: rumorTagValue(tags, 'decryption-nonce'),
        xHash: rumorTagValue(tags, 'x'),
        thumbUrl: rumorTagValue(tags, 'thumb'),
        dim: rumorTagValue(tags, 'dim'),
        blurhash: rumorTagValue(tags, 'blurhash')
    };
}

function formatConversationPreview(msg) {
    if (!msg) return 'No messages yet';
    if (msg.kind === 15 && msg.fileMeta) {
        const ft = msg.fileMeta.fileType || '';
        if (ft.startsWith('image/')) return '📷 Photo';
        if (ft.startsWith('audio/')) return '🎵 Audio';
        if (ft.startsWith('video/')) return '🎬 Video';
        return '📎 File';
    }
    const c = typeof msg.content === 'string' ? msg.content : '';
    if (!c) return '—';
    return `${c.substring(0, 50)}${c.length > 50 ? '...' : ''}`;
}

function normalizeReactionContent(content) {
    if (typeof content !== 'string') return null;
    const c = content.trim();
    if (!c) return null;
    if (c === '+') return '👍';
    if (c === '-') return '👎';
    return c.slice(0, 16);
}

function parseBolt11InvoiceFromText(content) {
    if (typeof content !== 'string') return null;
    const match = content.match(LIGHTNING_INVOICE_RE);
    if (!match) return null;
    const invoice = (match[2] || '').toLowerCase();
    if (!invoice) return null;
    const decoded = decodeInvoice(invoice);
    if (!decoded) return null;

    const cleanedText = (content.replace(match[0], ' ').replace(/\s+/g, ' ').trim());
    return {
        invoice,
        cleanedText,
        decoded
    };
}

function revokeActiveMessageBlobs() {
    for (const u of activeMessageBlobUrls) {
        try {
            URL.revokeObjectURL(u);
        } catch {
            /* ignore */
        }
    }
    activeMessageBlobUrls.clear();
}

function trimUrlTrailingPunctuation(url) {
    let u = url;
    while (u.length && /[.,;:!?)\]}>'"\u201d\u2019]$/.test(u)) {
        u = u.slice(0, -1);
    }
    return u;
}

function looksLikeDirectImageUrl(url) {
    return /\.(png|jpe?g|gif|webp|avif|svg)(\?|#|$)/i.test(url);
}

function isSafeHttpUrl(url) {
    try {
        const u = new URL(url);
        return u.protocol === 'http:' || u.protocol === 'https:';
    } catch {
        return false;
    }
}

function hexToBytes(hex) {
    const s = String(hex || '')
        .replace(/^0x/i, '')
        .replace(/\s/g, '');
    if (!s.length || s.length % 2 !== 0 || !/^[0-9a-fA-F]+$/.test(s)) {
        return null;
    }
    const out = new Uint8Array(s.length / 2);
    for (let i = 0; i < out.length; i++) {
        out[i] = parseInt(s.slice(i * 2, i * 2 + 2), 16);
    }
    return out;
}

async function sha256HexOfBuffer(buf) {
    const digest = await crypto.subtle.digest('SHA-256', buf);
    return [...new Uint8Array(digest)].map((b) => b.toString(16).padStart(2, '0')).join('');
}

async function decryptAesGcmRaw(keyBytes, ivBytes, cipherWithTag) {
    const cryptoKey = await crypto.subtle.importKey('raw', keyBytes, { name: 'AES-GCM' }, false, ['decrypt']);
    return new Uint8Array(
        await crypto.subtle.decrypt({ name: 'AES-GCM', iv: ivBytes }, cryptoKey, cipherWithTag)
    );
}

/**
 * Try NIP-17 kind-15 AES-GCM: ciphertext at URL, `x` = SHA-256 of ciphertext.
 * @returns {Promise<string|null>} object URL for decrypted bytes
 */
async function tryDecryptKind15ToBlobUrl(meta) {
    if (!meta?.url || !isSafeHttpUrl(meta.url) || meta.encryptionAlgorithm !== 'aes-gcm') return null;
    const keyBytes = hexToBytes(meta.decryptionKey);
    const nonceBytes = hexToBytes(meta.decryptionNonce);
    if (!keyBytes || !nonceBytes) return null;
    if (![16, 24, 32].includes(keyBytes.length)) return null;
    if (![12, 16].includes(nonceBytes.length)) return null;

    let res;
    try {
        res = await fetch(meta.url, { mode: 'cors', credentials: 'omit' });
    } catch {
        return null;
    }
    if (!res.ok) return null;
    const buf = await res.arrayBuffer();
    const ct = new Uint8Array(buf);

    if (meta.xHash) {
        const expected = meta.xHash.replace(/^0x/i, '').toLowerCase();
        try {
            const h = await sha256HexOfBuffer(ct);
            if (h !== expected) return null;
        } catch {
            return null;
        }
    }

    let plain;
    try {
        plain = await decryptAesGcmRaw(keyBytes, nonceBytes, ct);
    } catch {
        return null;
    }

    const mime =
        typeof meta.fileType === 'string' && meta.fileType.startsWith('image/')
            ? meta.fileType
            : 'application/octet-stream';
    const blob = new Blob([plain], { type: mime });
    const blobUrl = URL.createObjectURL(blob);
    activeMessageBlobUrls.add(blobUrl);
    return blobUrl;
}

/**
 * Append text with http(s) links and inline images (safe DOM only).
 * @param {HTMLElement} parent
 * @param {string} text
 * @param {{ bare?: boolean }} [opts] — bare: omit .message-text (e.g. nested in file card)
 */
function appendRichMessageContent(parent, text, opts = {}) {
    if (text == null || text === '') return;
    const inner = document.createElement('div');
    inner.className = opts.bare ? 'message-text-rich' : 'message-text message-text-rich';
    fillRichTextInto(inner, String(text));
    parent.appendChild(inner);
}

function fillRichTextInto(el, text) {
    el.textContent = '';
    if (!text) return;

    const re = new RegExp(HTTP_URL_IN_TEXT_RE.source, HTTP_URL_IN_TEXT_RE.flags);
    let last = 0;
    let m;
    let any = false;
    while ((m = re.exec(text)) !== null) {
        any = true;
        if (m.index > last) {
            el.appendChild(document.createTextNode(text.slice(last, m.index)));
        }
        const raw = m[0];
        const url = trimUrlTrailingPunctuation(raw);
        last = m.index + raw.length;

        if (!isSafeHttpUrl(url)) {
            el.appendChild(document.createTextNode(raw));
            continue;
        }

        if (looksLikeDirectImageUrl(url)) {
            const wrap = document.createElement('div');
            wrap.className = 'message-inline-image-wrap';
            const link = document.createElement('a');
            link.href = url;
            link.target = '_blank';
            link.rel = 'noopener noreferrer';
            link.className = 'message-inline-image-link';
            const img = document.createElement('img');
            img.className = 'message-inline-image';
            img.alt = '';
            img.loading = 'lazy';
            img.decoding = 'async';
            img.referrerPolicy = 'no-referrer';
            img.src = url;
            img.addEventListener(
                'error',
                () => {
                    wrap.replaceChildren();
                    const a = document.createElement('a');
                    a.href = url;
                    a.target = '_blank';
                    a.rel = 'noopener noreferrer';
                    a.className = 'message-link';
                    a.textContent = url;
                    wrap.appendChild(a);
                },
                { once: true }
            );
            link.appendChild(img);
            wrap.appendChild(link);
            el.appendChild(wrap);
        } else {
            const a = document.createElement('a');
            a.href = url;
            a.target = '_blank';
            a.rel = 'noopener noreferrer';
            a.className = 'message-link';
            a.textContent = url;
            el.appendChild(a);
        }
    }
    if (!any) {
        el.textContent = text;
        return;
    }
    if (last < text.length) {
        el.appendChild(document.createTextNode(text.slice(last)));
    }
}

function appendInlineImageFromBlobUrl(parent, blobUrl) {
    const wrap = document.createElement('div');
    wrap.className = 'message-inline-image-wrap';
    const img = document.createElement('img');
    img.className = 'message-inline-image';
    img.alt = '';
    img.decoding = 'async';
    img.src = blobUrl;
    wrap.appendChild(img);
    parent.appendChild(wrap);
}

/**
 * Kind 15 image: try AES-GCM decrypt, else direct <img> if URL is reachable as image.
 */
async function loadKind15ImagePreview(previewEl, meta) {
    previewEl.textContent = '';
    if (!meta?.fileType?.startsWith('image/')) {
        previewEl.hidden = true;
        return;
    }
    previewEl.hidden = false;

    const loading = document.createElement('div');
    loading.className = 'file-message-preview-loading';
    loading.textContent = 'Loading…';
    previewEl.appendChild(loading);

    const tryBlob = await tryDecryptKind15ToBlobUrl(meta);
    if (tryBlob) {
        loading.remove();
        appendInlineImageFromBlobUrl(previewEl, tryBlob);
        return;
    }

    if (!meta.encryptionAlgorithm && meta.url && isSafeHttpUrl(meta.url) && looksLikeDirectImageUrl(meta.url)) {
        loading.remove();
        const wrap = document.createElement('div');
        wrap.className = 'message-inline-image-wrap';
        const link = document.createElement('a');
        link.href = meta.url;
        link.target = '_blank';
        link.rel = 'noopener noreferrer';
        link.className = 'message-inline-image-link';
        const img = document.createElement('img');
        img.className = 'message-inline-image';
        img.alt = '';
        img.loading = 'lazy';
        img.referrerPolicy = 'no-referrer';
        img.src = meta.url;
        img.addEventListener(
            'error',
            () => {
                wrap.replaceChildren();
                const err = document.createElement('div');
                err.className = 'file-message-preview-note';
                err.textContent = 'Could not load image (check link or CORS).';
                wrap.appendChild(err);
            },
            { once: true }
        );
        link.appendChild(img);
        wrap.appendChild(link);
        previewEl.appendChild(wrap);
        return;
    }

    if (meta.encryptionAlgorithm === 'aes-gcm' && meta.url) {
        loading.remove();
        const fallbackBubble = document.createElement('div');
        fallbackBubble.className = 'file-message-fallback-bubble';
        appendRichMessageContent(fallbackBubble, meta.url, { bare: true });
        previewEl.appendChild(fallbackBubble);
        return;
    }

    loading.remove();
}

async function payLightningInvoice(invoice) {
    if (!invoice) {
        throw new Error('Missing invoice');
    }
    const webln = window.webln;
    if (!webln || typeof webln.sendPayment !== 'function') {
        throw new Error('No WebLN wallet found');
    }
    if (typeof webln.enable === 'function') {
        await webln.enable();
    }
    return webln.sendPayment(invoice);
}

function applyReactionToMessage(message, emoji, fromPubkey) {
    if (!message.reactions) {
        message.reactions = {};
    }
    if (!message.reactions[emoji]) {
        message.reactions[emoji] = { count: 0, reactors: [] };
    }
    const bucket = message.reactions[emoji];
    if (!bucket.reactors.includes(fromPubkey)) {
        bucket.reactors.push(fromPubkey);
        bucket.count += 1;
    }
}

function applyPendingReactionsForMessage(conversationPubkey, message) {
    if (!message?.id) return;
    const pending = pendingReactionsByMessageId.get(message.id);
    if (!pending?.length) return;

    for (const reaction of pending) {
        if (reaction.conversationPubkey !== conversationPubkey) continue;
        applyReactionToMessage(message, reaction.emoji, reaction.fromPubkey);
    }

    const remaining = pending.filter((reaction) => reaction.conversationPubkey !== conversationPubkey);
    if (remaining.length) {
        pendingReactionsByMessageId.set(message.id, remaining);
    } else {
        pendingReactionsByMessageId.delete(message.id);
    }
}

function handleReactionRumor(rumor, conversationPubkey, authorPubkey) {
    const kindTag = Array.isArray(rumor.tags)
        ? rumor.tags.find((t) => t[0] === 'k' && typeof t[1] === 'string')
        : null;
    if (kindTag && kindTag[1] !== '14' && kindTag[1] !== '15') {
        return false;
    }

    const eTag = Array.isArray(rumor.tags)
        ? rumor.tags.find((t) => t[0] === 'e' && typeof t[1] === 'string' && t[1].length)
        : null;
    if (!eTag) {
        return false;
    }
    const targetMessageId = eTag[1];
    const emoji = normalizeReactionContent(rumor.content);
    if (!emoji) {
        return false;
    }

    if (!conversations[conversationPubkey]) {
        conversations[conversationPubkey] = [];
    }

    const targetMessage = conversations[conversationPubkey].find((m) => m.id === targetMessageId);
    if (targetMessage) {
        applyReactionToMessage(targetMessage, emoji, authorPubkey);
    } else {
        const pending = pendingReactionsByMessageId.get(targetMessageId) || [];
        pending.push({ conversationPubkey, emoji, fromPubkey: authorPubkey });
        pendingReactionsByMessageId.set(targetMessageId, pending);
        scheduleGapFillForConversation(conversationPubkey);
    }
    return true;
}

function subscribeToMessages() {
    // Subscribe to kind 1059 (gift-wrapped) events tagged with our pubkey
    // SimplePool.subscribe automatically queries all connected relays
    // Store the subscription so it stays alive
    console.log('Setting up subscription for publicKey:', publicKey);
    const readRelays = getReadRelayUrls();
    console.log('Subscribing to relays:', readRelays);

    let eventCount = 0;

    // Create filter for gift-wrapped messages (kind 1059) tagged with our pubkey
    // Note: pool.subscribe takes a single filter object, not an array
    // Remove 'since' to get all historical messages, not just recent ones
    const filter = {
        kinds: [1059],
        '#p': [publicKey]
    };
    console.log('Subscription filter:', JSON.stringify(filter, null, 2));

    messageSubscription = pool.subscribe(readRelays, filter, {
        onevent(event) {
            eventCount++;
            const isDup = seenGiftWrapEventIds.has(event.id);
            console.log(`✅ Received gift-wrapped message #${eventCount}${isDup ? ' (duplicate)' : ''}:`, {
                id: event.id,
                kind: event.kind,
                created_at: new Date(event.created_at * 1000).toISOString(),
                tags: event.tags
            });

            handleGiftWrappedMessage(event).catch((error) => {
                console.error('Error in handleGiftWrappedMessage (non-blocking):', error);
            });
        },
        oneose() {
            console.log(`📭 EOSE (End of Stored Events) - received ${eventCount} total events, ${seenGiftWrapEventIds.size} unique ids`);
        }
    });

    console.log('✅ Subscription active - listening for messages on', readRelays.length, 'relays');
    console.log('💡 Querying all historical messages (no time limit)');
}

function scheduleMobileCatchup(reason = 'unknown') {
    if (!pool || !publicKey) return;
    if (mobileCatchupTimer) {
        clearTimeout(mobileCatchupTimer);
    }
    mobileCatchupTimer = setTimeout(() => {
        mobileCatchupTimer = null;
        console.log('Running mobile catch-up:', reason);
        try {
            if (messageSubscription) {
                messageSubscription.close();
            }
        } catch (e) {
            console.warn('Closing message subscription during catch-up failed:', e);
        }
        messageSubscription = null;
        subscribeToMessages();
        void fetchHistoricalGiftWraps();
    }, 350);
}

/** @param {{ suppressUi?: boolean }} [options] — suppressUi: batch historical load (single UI refresh at end). */
async function handleGiftWrappedMessage(giftWrap, options = {}) {
    if (seenGiftWrapEventIds.has(giftWrap.id)) {
        return;
    }
    seenGiftWrapEventIds.add(giftWrap.id);

    console.log('Processing gift-wrapped message:', {
        id: giftWrap.id,
        kind: giftWrap.kind,
        pubkey: giftWrap.pubkey,
        tags: giftWrap.tags
    });

    try {
        // Step 1: Unwrap the gift wrap (kind 1059) using NIP-44
        // Gift wrap is encrypted FROM ephemeral key TO our public key
        // We decrypt using our private key via the extension
        if (!window.nostr?.nip44?.decrypt) {
            console.error('Extension does not support nip44.decrypt. Please reconnect with a compatible extension.');
            return;
        }
        
        console.log('Decrypting gift wrap with ephemeral pubkey:', giftWrap.pubkey);
        let unwrappedJSON;
        try {
            unwrappedJSON = await window.nostr.nip44.decrypt(
                giftWrap.pubkey,
                giftWrap.content
            );
            console.log('Successfully decrypted gift wrap');
        } catch (decryptError) {
            // If decryption fails, this might be a message not intended for us
            // or encrypted with a different key/version. Skip it silently.
            console.warn('Failed to decrypt gift wrap (may not be for us or wrong encryption):', {
                error: decryptError.message,
                eventId: giftWrap.id,
                ephemeralPubkey: giftWrap.pubkey
            });
            return; // Skip this message, continue with others
        }
        
        const seal = JSON.parse(unwrappedJSON);
        console.log('Unwrapped seal:', { kind: seal.kind, pubkey: seal.pubkey });
        
        // Step 2: Verify it's a seal (kind 13)
        if (seal.kind !== 13) {
            console.error('Expected kind 13 seal, got:', seal.kind);
            return;
        }

        // Step 3: Decrypt the seal to get the rumor (NIP-17: kind 14 chat, 7 reaction, 15 file, …)
        // NIP-44 peer for decrypt is always the *other* party in the conversation:
        // - Incoming: seal author is the sender → decrypt(seal.pubkey, …).
        // - Our own sender copy: seal author is us; payload was encrypt(recipient, …) → decrypt(recipient, …).
        const sealAuthor = normalizePubkey(seal.pubkey);
        let sealDecryptPeer = seal.pubkey;
        if (sealAuthor === publicKey) {
            const sealPTag = Array.isArray(seal.tags)
                ? seal.tags.find((t) => t[0] === 'p' && typeof t[1] === 'string' && t[1].length)
                : null;
            if (!sealPTag) {
                console.warn(
                    'Skipping own kind 13 seal without p tag (cannot determine NIP-44 peer; re-send from updated app to fix).',
                    { eventId: giftWrap.id }
                );
                return;
            }
            sealDecryptPeer = normalizePubkey(sealPTag[1]);
        }

        console.log('Decrypting seal; nip44 peer:', sealDecryptPeer);
        let rumorJSON;
        try {
            rumorJSON = await window.nostr.nip44.decrypt(sealDecryptPeer, seal.content);
            console.log('Successfully decrypted seal');
        } catch (decryptError) {
            // If seal decryption fails, skip this message
            console.warn('Failed to decrypt seal (may not be for us or wrong encryption):', {
                error: decryptError.message,
                eventId: giftWrap.id,
                sealAuthor: seal.pubkey,
                nip44Peer: sealDecryptPeer
            });
            return; // Skip this message, continue with others
        }
        
        const rumor = JSON.parse(rumorJSON);
        console.log('Unwrapped rumor:', { kind: rumor.kind, pubkey: rumor.pubkey, content: rumor.content?.substring(0, 50) });

        try {
            // Step 4: NIP-17 — kind 14 DMs, kind 7 reactions, kind 15 file messages (see nips/17.md).
            if (rumor.kind !== 14 && rumor.kind !== 7 && rumor.kind !== 15) {
                console.warn('Unsupported rumor kind inside gift wrap (skipping):', rumor.kind);
                return;
            }

            // Step 5: Verify the sender
            if (normalizePubkey(seal.pubkey) !== normalizePubkey(rumor.pubkey)) {
                console.error('Sender pubkey mismatch - potential impersonation attempt');
                return;
            }

            const authorPubkey = normalizePubkey(rumor.pubkey);
            const conversationPubkey = getRumorConversationPubkey(rumor, authorPubkey);
            if (!conversationPubkey) {
                console.error('Outgoing rumor missing p tag; cannot assign conversation');
                return;
            }

            if (!conversations[conversationPubkey]) {
                conversations[conversationPubkey] = [];
            }

            if (rumor.id) {
                if (seenRumorIds.has(rumor.id)) {
                    return;
                }
                seenRumorIds.add(rumor.id);
            }

            if (rumor.kind === 7) {
                const applied = handleReactionRumor(rumor, conversationPubkey, authorPubkey);
                if (!applied) {
                    return;
                }
                if (!options.suppressUi) {
                    if (currentChat === conversationPubkey) {
                        queueActiveChatRender(conversationPubkey);
                    }
                    updateConversationsList();
                }
                return;
            }

            // Same logical message can appear locally first, then again from our self-addressed gift wrap
            if (rumor.id && conversations[conversationPubkey].some((m) => m.id === rumor.id)) {
                return;
            }

            if (rumor.kind === 15) {
                const fileMeta = parseKind15FileMeta(rumor);
                if (!fileMeta) {
                    console.warn('Kind 15 rumor missing file URL; skipping', { id: rumor.id });
                    return;
                }
                conversations[conversationPubkey].push({
                    id: rumor.id,
                    kind: 15,
                    content: rumor.content,
                    fileMeta,
                    timestamp: rumor.created_at,
                    from: authorPubkey,
                    actualTimestamp: giftWrap.created_at
                });
            } else {
                conversations[conversationPubkey].push({
                    id: rumor.id,
                    kind: 14,
                    content: rumor.content,
                    timestamp: rumor.created_at,
                    from: authorPubkey,
                    actualTimestamp: giftWrap.created_at
                });
            }
            applyPendingReactionsForMessage(
                conversationPubkey,
                conversations[conversationPubkey][conversations[conversationPubkey].length - 1]
            );

            conversations[conversationPubkey].sort((a, b) => a.timestamp - b.timestamp);

            if (!options.suppressUi) {
                updateConversationsList();
                if (currentChat === conversationPubkey) {
                    queueActiveChatRender(conversationPubkey, { header: true });
                }
                if (!userProfiles[conversationPubkey]) {
                    void fetchUserProfile(conversationPubkey).then(() => {
                        queueConversationsListUpdate();
                        queueChatHeaderUpdate(conversationPubkey);
                    });
                }
            }
        } finally {
            noteInboxGiftWrapProcessed(giftWrap.created_at);
        }

    } catch (error) {
        // Catch any other unexpected errors (JSON parsing, etc.)
        // Log but don't throw - we want to continue processing other messages
        console.error('Unexpected error processing gift-wrapped message:', error);
        console.error('Error details:', {
            message: error.message,
            giftWrap: giftWrap ? { id: giftWrap.id, kind: giftWrap.kind } : null
        });
        // Return silently - don't let one bad message stop processing others
        return;
    }
}

function lastConversationSortTime(conv) {
    if (!conv || conv.length === 0) {
        return 0;
    }
    return conv[conv.length - 1].timestamp;
}

function avatarInitialFromLabel(label, pubkey = '') {
    const base = (label || '').trim();
    if (base) {
        return base.slice(0, 1).toUpperCase();
    }
    return (pubkey || '?').slice(0, 1).toUpperCase();
}

function createAvatarNode(pubkey, className = 'avatar') {
    const profile = userProfiles[pubkey];
    const picture = typeof profile?.picture === 'string' ? profile.picture.trim() : '';
    const canUsePicture = picture.length > 0 && !brokenAvatarUrls.has(picture);
    const avatar = canUsePicture ? document.createElement('img') : document.createElement('div');
    avatar.className = className;

    if (canUsePicture) {
        avatar.classList.add('avatar-image');
        avatar.classList.remove('is-loaded');
        avatar.decoding = 'async';
        avatar.src = picture;
        avatar.alt = '';
        avatar.loading = 'lazy';
        avatar.referrerPolicy = 'no-referrer';
        avatar.addEventListener('load', () => {
            avatar.classList.add('is-loaded');
        }, { once: true });
        avatar.addEventListener('error', () => {
            brokenAvatarUrls.add(picture);
            const fallback = document.createElement('div');
            fallback.className = className;
            fallback.textContent = avatarInitialFromLabel(getDisplayName(pubkey), pubkey);
            avatar.replaceWith(fallback);
        });
        return avatar;
    }

    avatar.textContent = avatarInitialFromLabel(getDisplayName(pubkey), pubkey);
    return avatar;
}

function updateAvatarHost(host, pubkey) {
    const profile = userProfiles[pubkey];
    const picture = typeof profile?.picture === 'string' ? profile.picture.trim() : '';
    const canUsePicture = picture.length > 0 && !brokenAvatarUrls.has(picture);
    let avatar = host.firstElementChild;

    if (canUsePicture) {
        if (!(avatar instanceof HTMLImageElement)) {
            host.innerHTML = '';
            avatar = document.createElement('img');
            avatar.className = 'avatar';
            avatar.alt = '';
            avatar.referrerPolicy = 'no-referrer';
            avatar.decoding = 'async';
            host.appendChild(avatar);
        }
        if (avatar.dataset.avatarSrc !== picture) {
            avatar.classList.add('avatar-image');
            avatar.classList.remove('is-loaded');
            avatar.dataset.avatarSrc = picture;
            avatar.addEventListener('load', () => {
                avatar.classList.add('is-loaded');
            }, { once: true });
            avatar.src = picture;
        }
        avatar.onerror = () => {
            brokenAvatarUrls.add(picture);
            updateAvatarHost(host, pubkey);
        };
        return;
    }

    if (!(avatar instanceof HTMLDivElement)) {
        host.innerHTML = '';
        avatar = document.createElement('div');
        avatar.className = 'avatar';
        host.appendChild(avatar);
    }
    avatar.textContent = avatarInitialFromLabel(getDisplayName(pubkey), pubkey);
}

function createConversationItem(pubkey) {
    const item = document.createElement('div');
    item.className = 'conversation-item';
    item.onclick = () => openChat(pubkey);

    const main = document.createElement('div');
    main.className = 'conversation-item-main';

    const avatarHost = document.createElement('div');
    avatarHost.className = 'conversation-item-avatar-host';

    const content = document.createElement('div');
    content.className = 'conversation-item-content';

    const top = document.createElement('div');
    top.className = 'conversation-item-top';

    const nameEl = document.createElement('div');
    nameEl.className = 'conversation-pubkey';

    const dateEl = document.createElement('div');
    dateEl.className = 'conversation-date';

    const previewEl = document.createElement('div');
    previewEl.className = 'conversation-preview';

    top.appendChild(nameEl);
    top.appendChild(dateEl);
    content.appendChild(top);
    content.appendChild(previewEl);
    main.appendChild(avatarHost);
    main.appendChild(content);
    item.appendChild(main);

    return { item, avatarHost, nameEl, dateEl, previewEl };
}

function updateConversationsList() {
    const list = document.getElementById('conversationsList');
    const orderedPubkeys = Object.keys(conversations).sort(
        (a, b) => lastConversationSortTime(conversations[b]) - lastConversationSortTime(conversations[a])
    );
    const seen = new Set();

    for (const pubkey of orderedPubkeys) {
        seen.add(pubkey);
        const conv = conversations[pubkey];
        const lastMsg = conv.length > 0 ? conv[conv.length - 1] : null;
        const displayName = getDisplayName(pubkey);
        const dateIndicator = lastMsg ? formatConversationDate(lastMsg.timestamp) : '';
        const preview = formatConversationPreview(lastMsg);

        let row = conversationItemEls.get(pubkey);
        if (!row) {
            row = createConversationItem(pubkey);
            conversationItemEls.set(pubkey, row);
        }

        row.item.className = 'conversation-item' + (currentChat === pubkey ? ' active' : '');
        row.nameEl.textContent = displayName;
        row.dateEl.textContent = dateIndicator;
        row.previewEl.textContent = preview;
        updateAvatarHost(row.avatarHost, pubkey);
        list.appendChild(row.item);
    }

    for (const [pubkey, row] of conversationItemEls.entries()) {
        if (!seen.has(pubkey)) {
            row.item.remove();
            conversationItemEls.delete(pubkey);
        }
    }
}

function isMobileLayout() {
    return window.matchMedia('(max-width: 768px)').matches;
}

function setMobileChatPanel(open) {
    document.querySelector('.container')?.classList.toggle('mobile-chat-visible', open);
}

function openChat(pubkey) {
    currentChat = normalizePubkey(pubkey);
    document.getElementById('emptyState').style.display = 'none';
    document.getElementById('chatView').style.display = 'flex';

    // Show the chat column before measuring scroll (mobile hides it until this class is set).
    if (isMobileLayout()) {
        setMobileChatPanel(true);
    }

    updateChatHeader(pubkey);
    displayMessages(pubkey);
    updateConversationsList();
    void fetchConversationRepair(currentChat, { deep: true });
}

function backToConversations() {
    setMobileChatPanel(false);
}

window.backToConversations = backToConversations;

// Update chat header with display name
function updateChatHeader(pubkey) {
    const displayName = getDisplayName(pubkey);
    const avatarHost = document.getElementById('currentChatAvatar');
    const npubEl = document.getElementById('currentChatNpub');
    const copyBtn = document.getElementById('copyCurrentChatNpubBtn');

    if (avatarHost) {
        updateAvatarHost(avatarHost, pubkey);
    }

    const npub = nip19.npubEncode(pubkey);
    const npubShort = npub.length > 22 ? `${npub.slice(0, 11)}:${npub.slice(-11)}` : npub;
    document.getElementById('currentChatPubkey').textContent = displayName;

    if (npubEl) {
        npubEl.textContent = npubShort;
        npubEl.title = npub;
    }
    if (copyBtn) {
        copyBtn.onclick = async (e) => {
            e.stopPropagation();
            const original = copyBtn.textContent;
            try {
                await navigator.clipboard.writeText(npub);
                copyBtn.textContent = '✓';
            } catch {
                copyBtn.textContent = '!';
            }
            setTimeout(() => {
                copyBtn.textContent = original || '⧉';
            }, 1200);
        };
    }
}

// Format timestamp with date and time
function formatTimestamp(timestamp) {
    const date = new Date(timestamp * 1000);
    const now = new Date();
    const today = new Date(now.getFullYear(), now.getMonth(), now.getDate());
    const messageDate = new Date(date.getFullYear(), date.getMonth(), date.getDate());
    
    // Check if message is from today
    if (messageDate.getTime() === today.getTime()) {
        // Today: show only time
        return date.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
    } else {
        // Not today: show date and time
        return date.toLocaleString([], { 
            month: 'short', 
            day: 'numeric', 
            hour: '2-digit', 
            minute: '2-digit' 
        });
    }
}

// Format date for separators (e.g., "Today", "Yesterday", "Dec 25")
function formatDateSeparator(timestamp) {
    const date = new Date(timestamp * 1000);
    const now = new Date();
    const today = new Date(now.getFullYear(), now.getMonth(), now.getDate());
    const yesterday = new Date(today);
    yesterday.setDate(yesterday.getDate() - 1);
    const messageDate = new Date(date.getFullYear(), date.getMonth(), date.getDate());
    
    if (messageDate.getTime() === today.getTime()) {
        return 'Today';
    } else if (messageDate.getTime() === yesterday.getTime()) {
        return 'Yesterday';
    } else {
        return date.toLocaleDateString([], { month: 'long', day: 'numeric', year: date.getFullYear() !== now.getFullYear() ? 'numeric' : undefined });
    }
}

// Format date for conversation list (shorter format)
function formatConversationDate(timestamp) {
    const date = new Date(timestamp * 1000);
    const now = new Date();
    const today = new Date(now.getFullYear(), now.getMonth(), now.getDate());
    const yesterday = new Date(today);
    yesterday.setDate(yesterday.getDate() - 1);
    const messageDate = new Date(date.getFullYear(), date.getMonth(), date.getDate());
    
    if (messageDate.getTime() === today.getTime()) {
        // Today: show time
        return date.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
    } else if (messageDate.getTime() === yesterday.getTime()) {
        return 'Yesterday';
    } else {
        // Older: show short date
        const daysDiff = Math.floor((today - messageDate) / (1000 * 60 * 60 * 24));
        if (daysDiff < 7) {
            // Within a week: show day name
            return date.toLocaleDateString([], { weekday: 'short' });
        } else if (date.getFullYear() === now.getFullYear()) {
            // This year: show month and day
            return date.toLocaleDateString([], { month: 'short', day: 'numeric' });
        } else {
            // Older: show month, day, year
            return date.toLocaleDateString([], { month: 'short', day: 'numeric', year: '2-digit' });
        }
    }
}

function displayMessages(pubkey) {
    const container = document.getElementById('messagesContainer');
    revokeActiveMessageBlobs();
    container.innerHTML = '';

    if (!conversations[pubkey]) return;

    let lastDate = null;

    conversations[pubkey].forEach((msg, index) => {
        const msgDate = new Date(msg.timestamp * 1000);
        const currentDate = new Date(msgDate.getFullYear(), msgDate.getMonth(), msgDate.getDate());
        
        // Add date separator if this is a new day
        if (lastDate === null || currentDate.getTime() !== lastDate.getTime()) {
            const dateSeparator = document.createElement('div');
            dateSeparator.className = 'date-separator';
            dateSeparator.textContent = formatDateSeparator(msg.timestamp);
            container.appendChild(dateSeparator);
            lastDate = currentDate;
        }

        const div = document.createElement('div');
        div.className = 'message ' + (msg.from === publicKey ? 'sent' : 'received');

        const bodyEl = document.createElement('div');
        bodyEl.className = 'message-body';
        if (msg.kind === 15 && msg.fileMeta) {
            const isImage = (msg.fileMeta.fileType || '').startsWith('image/');
            if (isImage) {
                div.classList.add('message-invoice');
                const previewEl = document.createElement('div');
                previewEl.className = 'file-message-preview';
                previewEl.hidden = false;
                bodyEl.appendChild(previewEl);
                void loadKind15ImagePreview(previewEl, msg.fileMeta);
            } else {
                div.classList.add('message-invoice');
                const fileCard = document.createElement('div');
                fileCard.className = 'file-message-card';

                const meta = document.createElement('div');
                meta.className = 'file-message-card-meta';
                meta.textContent = msg.fileMeta.fileType || 'File attachment';
                if (msg.fileMeta.dim) {
                    meta.textContent += ` · ${msg.fileMeta.dim}`;
                }

                const linkRow = document.createElement('div');
                linkRow.className = 'file-message-card-links';
                appendRichMessageContent(linkRow, msg.fileMeta.url, { bare: true });

                fileCard.appendChild(meta);
                fileCard.appendChild(linkRow);
                bodyEl.appendChild(fileCard);
            }
        } else {
        const parsedInvoice = parseBolt11InvoiceFromText(msg.content);
        if (parsedInvoice) {
            div.classList.add('message-invoice');
            if (parsedInvoice.cleanedText) {
                appendRichMessageContent(bodyEl, parsedInvoice.cleanedText);
            }

            const invoiceCard = document.createElement('div');
            invoiceCard.className = 'invoice-card';

            const top = document.createElement('div');
            top.className = 'invoice-card-top';

            const header = document.createElement('div');
            header.className = 'invoice-card-header';
            header.textContent = 'Lightning Invoice';

            const copyIconBtn = document.createElement('button');
            copyIconBtn.type = 'button';
            copyIconBtn.className = 'invoice-copy-icon-btn';
            copyIconBtn.setAttribute('aria-label', 'Copy invoice');
            copyIconBtn.textContent = '⧉';
            copyIconBtn.addEventListener('click', async (e) => {
                e.stopPropagation();
                try {
                    await navigator.clipboard.writeText(parsedInvoice.invoice);
                    copyIconBtn.textContent = '✓';
                    setTimeout(() => {
                        copyIconBtn.textContent = '⧉';
                    }, 1200);
                } catch {
                    copyIconBtn.textContent = '!';
                    setTimeout(() => {
                        copyIconBtn.textContent = '⧉';
                    }, 1200);
                }
            });
            top.appendChild(header);
            top.appendChild(copyIconBtn);

            const amount = document.createElement('div');
            amount.className = 'invoice-card-amount';
            amount.textContent = parsedInvoice.decoded?.satoshi
                ? `${Math.round(parsedInvoice.decoded.satoshi).toLocaleString()} sats`
                : 'Amount encoded in invoice';

            const actions = document.createElement('div');
            actions.className = 'invoice-card-actions';
            const payBtn = document.createElement('button');
            payBtn.type = 'button';
            payBtn.className = 'invoice-pay-btn';
            payBtn.textContent = 'Pay';
            payBtn.addEventListener('click', async (e) => {
                e.stopPropagation();
                const previous = payBtn.textContent;
                payBtn.disabled = true;
                payBtn.textContent = 'Paying…';
                try {
                    await payLightningInvoice(parsedInvoice.invoice);
                    payBtn.textContent = 'Paid';
                    setTimeout(() => {
                        payBtn.textContent = previous;
                        payBtn.disabled = false;
                    }, 1400);
                } catch (err) {
                    payBtn.textContent = err?.message?.includes('No WebLN') ? 'No wallet' : 'Failed';
                    setTimeout(() => {
                        payBtn.textContent = previous;
                        payBtn.disabled = false;
                    }, 1400);
                }
            });
            actions.appendChild(payBtn);

            invoiceCard.appendChild(top);
            invoiceCard.appendChild(amount);
            invoiceCard.appendChild(actions);
            bodyEl.appendChild(invoiceCard);
        } else {
            appendRichMessageContent(bodyEl, typeof msg.content === 'string' ? msg.content : '');
        }
        }

        const timeEl = document.createElement('div');
        timeEl.className = 'message-time';
        timeEl.textContent = formatTimestamp(msg.timestamp);

        const canReact = Boolean(msg.id);
        if (canReact) {
            const actionsEl = document.createElement('div');
            actionsEl.className = 'message-actions';

            const reactBtn = document.createElement('button');
            reactBtn.type = 'button';
            reactBtn.className = 'message-react-btn';
            reactBtn.setAttribute('aria-label', 'React to message');
            reactBtn.textContent = '⋮';

            const picker = document.createElement('div');
            picker.className = 'message-reaction-picker';
            picker.hidden = true;
            picker.dataset.expanded = 'false';

            const quickRow = document.createElement('div');
            quickRow.className = 'message-reaction-picker-quick';

            const reactionSet = getReactionSet();
            reactionSet.quick.forEach((emoji) => {
                const b = createReactionOptionButton(emoji, picker, msg);
                quickRow.appendChild(b);
            });

            const moreBtn = document.createElement('button');
            moreBtn.type = 'button';
            moreBtn.className = 'message-reaction-option message-reaction-option--more';
            moreBtn.setAttribute('aria-label', 'More reactions');
            moreBtn.textContent = '+';
            quickRow.appendChild(moreBtn);
            picker.appendChild(quickRow);

            const expanded = document.createElement('div');
            expanded.className = 'message-reaction-expanded';
            expanded.hidden = true;

            reactionSet.extra.forEach((emoji) => {
                const b = createReactionOptionButton(emoji, picker, msg, () => {
                    expanded.hidden = true;
                    picker.dataset.expanded = 'false';
                    moreBtn.hidden = false;
                });
                expanded.appendChild(b);
            });

            moreBtn.addEventListener('click', (e) => {
                e.stopPropagation();
                const willOpen = expanded.hidden;
                expanded.hidden = !willOpen;
                picker.dataset.expanded = willOpen ? 'true' : 'false';
                moreBtn.hidden = willOpen;
            });

            const closeOtherPickers = () => {
                container.querySelectorAll('.message-reaction-picker').forEach((el) => {
                    if (el !== picker) {
                        el.hidden = true;
                        el.dataset.expanded = 'false';
                        const ex = el.querySelector('.message-reaction-expanded');
                        if (ex) ex.hidden = true;
                        const mb = el.querySelector('.message-reaction-option--more');
                        if (mb) mb.hidden = false;
                    }
                });
            };

            const togglePicker = (forceOpen = false) => {
                closeOtherPickers();
                picker.hidden = forceOpen ? false : !picker.hidden;
                if (picker.hidden) {
                    picker.dataset.expanded = 'false';
                    expanded.hidden = true;
                    moreBtn.hidden = false;
                }
            };

            reactBtn.addEventListener('click', (e) => {
                e.stopPropagation();
                togglePicker(false);
            });

            let longPressTimer = null;
            const clearLongPress = () => {
                if (longPressTimer) {
                    clearTimeout(longPressTimer);
                    longPressTimer = null;
                }
            };

            div.addEventListener('touchstart', (e) => {
                if (!isMobileLayout() || e.target.closest('.message-actions')) {
                    return;
                }
                clearLongPress();
                longPressTimer = setTimeout(() => {
                    togglePicker(true);
                }, 420);
            }, { passive: true });
            div.addEventListener('touchend', clearLongPress, { passive: true });
            div.addEventListener('touchcancel', clearLongPress, { passive: true });
            div.addEventListener('touchmove', clearLongPress, { passive: true });

            actionsEl.appendChild(reactBtn);
            picker.appendChild(expanded);
            actionsEl.appendChild(picker);
            div.appendChild(actionsEl);
        }

        div.appendChild(bodyEl);
        div.appendChild(timeEl);

        const reactionEntries = msg.reactions ? Object.entries(msg.reactions) : [];
        if (reactionEntries.length > 0) {
            div.classList.add('has-reactions');
            const reactionsEl = document.createElement('div');
            reactionsEl.className = 'message-reactions';

            reactionEntries
                .sort((a, b) => a[0].localeCompare(b[0]))
                .forEach(([emoji, info], index) => {
                    const pill = document.createElement('span');
                    pill.className = 'message-reaction-pill';
                    const shortcode = emojiShortcodeFromToken(emoji);
                    const url = shortcode ? customReactionEmojiUrlMap[shortcode] : '';
                    if (url) {
                        const img = document.createElement('img');
                        img.src = url;
                        img.alt = emoji;
                        img.className = 'message-reaction-pill-emoji';
                        img.referrerPolicy = 'no-referrer';
                        img.loading = 'lazy';
                        pill.appendChild(img);
                        pill.title = emoji;
                    } else {
                        pill.textContent = emoji;
                    }
                    pill.style.setProperty('--reaction-index', String(index));
                    if (Array.isArray(info?.reactors) && info.reactors.includes(publicKey)) {
                        pill.classList.add('is-own-reaction');
                    }
                    reactionsEl.appendChild(pill);
                });

            div.appendChild(reactionsEl);
        }

        container.appendChild(div);
    });

    const scrollToBottom = () => {
        container.scrollTop = container.scrollHeight;
    };
    scrollToBottom();
    // After flex/mobile layout paints, scrollHeight is final — rAF ensures we land on the latest message.
    requestAnimationFrame(() => {
        scrollToBottom();
        requestAnimationFrame(scrollToBottom);
    });
}

async function publishRumorAsGiftWrap(rumor, peerPubkey) {
    let recipientInboxRelays = await fetchKind10050Relays(peerPubkey);
    if (!recipientInboxRelays.length) {
        // Retry with a wider/ensured probe before declaring recipient not NIP-17 ready.
        recipientInboxRelays = await fetchKind10050Relays(peerPubkey, {
            relays: [...new Set([...RELAY_URLS, ...dmRelayUrls])],
            ensureConnections: true,
            maxWait: 15000
        });
    }
    if (!recipientInboxRelays.length) {
        throw new Error('Recipient kind 10050 inbox relays not discoverable right now.');
    }
    const publishRelays = [...new Set(recipientInboxRelays)];
    const relayHint = recipientInboxRelays[0] || null;

    const sealContent = JSON.stringify(rumor);
    const encryptedRumor = await window.nostr.nip44.encrypt(peerPubkey, sealContent);

    const sealTemplate = {
        kind: 13,
        pubkey: publicKey,
        created_at: getRandomPastTimestamp(),
        tags: relayHint ? [['p', peerPubkey, relayHint]] : [['p', peerPubkey]],
        content: encryptedRumor
    };

    const signedSeal = await window.nostr.signEvent(sealTemplate);
    const sealToWrap = {
        kind: 13,
        pubkey: signedSeal.pubkey ?? sealTemplate.pubkey,
        created_at: signedSeal.created_at ?? sealTemplate.created_at,
        tags: signedSeal.tags?.length ? signedSeal.tags : sealTemplate.tags,
        content: sealTemplate.content,
        id: signedSeal.id,
        sig: signedSeal.sig
    };
    if (!sealToWrap.id || !sealToWrap.sig) {
        throw new Error('Signing failed: missing id or sig');
    }

    await createAndPublishGiftWrap(sealToWrap, peerPubkey, publishRelays, relayHint, { requireSuccess: true });

    const selfInbox = await fetchKind10050Relays(publicKey);
    if (selfInbox.length > 0) {
        const selfPublishRelays = [...new Set(selfInbox)];
        await createAndPublishGiftWrap(sealToWrap, publicKey, selfPublishRelays, selfInbox[0] || null);
    } else {
        console.warn('Skipping self gift-wrap copy: no kind 10050 inbox relays for sender key.');
    }
}

async function sendReactionToMessage(message, emoji) {
    if (!currentChat || !message?.id) return;
    const normalizedEmoji = normalizeReactionContent(emoji);
    if (!normalizedEmoji) return;

    applyReactionToMessage(message, normalizedEmoji, publicKey);
    queueActiveChatRender(currentChat);

    try {
        const now = Math.floor(Date.now() / 1000);
        const rumor = {
            kind: 7,
            pubkey: publicKey,
            created_at: now,
            tags: [['e', message.id], ['k', String(message.kind || 14)], ['p', currentChat]],
            content: normalizedEmoji
        };
        rumor.id = getEventHash(rumor);
        await publishRumorAsGiftWrap(rumor, currentChat);
    } catch (error) {
        console.warn('Failed to publish reaction:', error);
    }
}

async function sendMessage() {
    const input = document.getElementById('messageInput');
    const sendBtn = document.getElementById('sendBtn');
    const content = input.value.trim();

    if (!content || !currentChat) return;

    sendBtn.disabled = true;
    sendBtn.innerHTML = '<div class="loading"></div>';

    try {
        const now = Math.floor(Date.now() / 1000);

        // Step 1: Create the rumor (kind 14) — unsigned; NIP-17 requires id + created_at (same as nostr-tools createRumor)
        const rumor = {
            kind: 14,
            pubkey: publicKey,
            created_at: now,
            tags: [['p', currentChat]],
            content: content
        };
        rumor.id = getEventHash(rumor);
        await publishRumorAsGiftWrap(rumor, currentChat);

        // Add to local conversation
        if (!conversations[currentChat]) {
            conversations[currentChat] = [];
        }

        conversations[currentChat].push({
            id: rumor.id,
            kind: 14,
            content: content,
            timestamp: now,
            from: publicKey
        });

        displayMessages(currentChat);
        updateConversationsList();
        input.value = '';

    } catch (error) {
        alert('Failed to send message: ' + error.message);
        console.error(error);
    } finally {
        sendBtn.disabled = false;
        sendBtn.innerHTML = '<svg viewBox="0 0 24 24"><path d="M2.01 21L23 12 2.01 3 2 10l15 2-15 2z"/></svg>';
    }
}

async function createAndPublishGiftWrap(seal, recipientPubkey, publishRelays, relayHint, options = {}) {
    // Generate random ephemeral key for this gift wrap
    // Note: Ephemeral keys are temporary and only used for gift wrapping
    // These are NOT user keys - they're generated per message for privacy
    const ephemeralKey = generateSecretKey();
    const ephemeralPubkey = getPublicKey(ephemeralKey);

    const recipientHex = normalizePubkey(recipientPubkey);

    // Encrypt the seal using NIP-44 with the ephemeral key
    // Note: We use nostr-tools nip44 here (not extension) because:
    // 1. The extension's nip44 uses the user's key
    // 2. Gift wrapping requires encryption FROM an ephemeral key TO the recipient
    // 3. Ephemeral keys are temporary and not stored in the extension
    const sealJSON = JSON.stringify(seal);

    // Get conversation key for ephemeral key -> recipient encryption
    // This is the only place we use nostr-tools nip44; all user operations use extension
    const conversationKey = getConversationKey(ephemeralKey, recipientHex);
    const encryptedSeal = nip44Encrypt(sealJSON, conversationKey);

    // Create gift wrap (kind 1059); optional third element on p matches NIP-17 / interop room identity
    const pTag = relayHint ? ['p', recipientHex, relayHint] : ['p', recipientHex];
    const giftWrap = {
        kind: 1059,
        pubkey: ephemeralPubkey,
        created_at: getRandomPastTimestamp(),
        tags: [pTag],
        content: encryptedSeal
    };

    // Sign the gift wrap with the ephemeral key
    const signedGiftWrap = finalizeEvent(giftWrap, ephemeralKey);

    // Publish to all relays
    // Use Promise.any() so we succeed if at least one relay accepts the event
    // This prevents timeout errors if some relays are slow or rejecting
    try {
        const targets = publishRelays?.length ? publishRelays : RELAY_URLS;
        const publishPromises = targets.map(async (url) => {
            try {
                await pool.publish([url], signedGiftWrap);
                return { success: true, url };
            } catch (err) {
                console.warn(`Failed to publish to ${url}:`, err);
                throw err; // Re-throw so Promise.any can handle it
            }
        });
        
        await Promise.any(publishPromises);
        console.log('Gift wrap published successfully to at least one relay');
    } catch (error) {
        if (options.requireSuccess) {
            throw new Error('Failed to publish gift wrap to recipient inbox relays.');
        }
        // If all relays fail for non-required copies, log but keep UI responsive.
        console.warn('Failed to publish optional gift wrap copy to all relays:', error);
    }
}

// Make functions available globally for onclick handlers
window.connectWithExtension = connectWithExtension;
window.sendMessage = sendMessage;

// Initialize DOM event listeners when DOM is ready
document.addEventListener('DOMContentLoaded', function() {
    const versionEl = document.getElementById('appVersion');
    if (versionEl) {
        versionEl.textContent = 'v' + pkg.version;
    }

    window.addEventListener('resize', function() {
        if (!isMobileLayout()) {
            setMobileChatPanel(false);
        }
    });

    const messageInput = document.getElementById('messageInput');
    if (messageInput) {
        // Auto-resize textarea
        messageInput.addEventListener('input', function() {
            this.style.height = 'auto';
            this.style.height = Math.min(this.scrollHeight, 150) + 'px';
        });

        // Send on Enter
        messageInput.addEventListener('keydown', function(e) {
            if (e.key === 'Enter' && !e.shiftKey) {
                e.preventDefault();
                sendMessage();
            }
        });
    }

    initEmojiPicker();
    initNewChatUi();
    initSettingsUi();
    initImageLightbox();

    document.addEventListener('visibilitychange', () => {
        if (document.visibilityState === 'visible') {
            scheduleMobileCatchup('visibility-resume');
        }
    });
    window.addEventListener('online', () => {
        scheduleMobileCatchup('network-online');
    });
});

