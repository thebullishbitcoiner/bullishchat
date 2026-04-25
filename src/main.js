import pkg from '../package.json';
import { SimplePool, generateSecretKey, getPublicKey, getEventHash, finalizeEvent } from 'nostr-tools';
import * as nip19 from 'nostr-tools/nip19';
// Note: nip44 is used for both ephemeral key operations and user key operations
// We check if extension provides nip44, otherwise fall back to library (but need private key access)
import { encrypt as nip44Encrypt, decrypt as nip44Decrypt, getConversationKey } from 'nostr-tools/nip44';

// Relay URLs to connect to
const RELAY_URLS = [
    'wss://relay.0xchat.com',
    'wss://relay.damus.io',
    'wss://relay.primal.net',
    'wss://auth.nostr1.com'
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

/** nostr.wine search (kind 0); free tier ~1 req/s */
const NOSTR_WINE_SEARCH_URL = 'https://api.nostr.wine/search';

let wineSearchAbort = null;
let wineSearchDebounceTimer = null;
let wineSearchSerial = 0;
let lastNostrWineRequestMs = 0;

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
    document.body.style.overflow = 'hidden';
    setTimeout(() => input.focus(), 50);
}

function closeNewChatModal() {
    const modal = document.getElementById('newChatModal');
    if (modal) {
        modal.hidden = true;
    }
    document.body.style.overflow = '';
    wineSearchAbort?.abort();
    if (wineSearchDebounceTimer) {
        clearTimeout(wineSearchDebounceTimer);
    }
    wineSearchSerial += 1;
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
        const modalEl = document.getElementById('newChatModal');
        if (modalEl && !modalEl.hidden) {
            closeNewChatModal();
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
            try {
                pool.destroy();
            } catch (e) {
                console.warn('Destroying previous relay pool:', e);
            }
        }
        pool = new SimplePool();
        
        // Connect to all relays
        document.getElementById('statusText').textContent = 'Connecting to relays...';
        const connectPromises = RELAY_URLS.map(async (url) => {
            try {
                const relay = await pool.ensureRelay(url);
                console.log('Connected to relay:', url);
                return { url, success: true, relay };
            } catch (error) {
                console.warn('Failed to connect to relay:', url, error);
                return { url, success: false, error };
            }
        });
        
        const results = await Promise.allSettled(connectPromises);
        const relayResults = results
            .filter((r) => r.status === 'fulfilled')
            .map((r) => ({ url: r.value.url, success: r.value.success }));
        const successfulConnections = relayResults.filter((r) => r.success).length;

        document.getElementById('statusDot').classList.add('connected');
        document.getElementById('statusText').textContent = `Connected to ${successfulConnections}/${RELAY_URLS.length} relays`;
        document.getElementById('connectionSetup').style.display = 'none';
        document.body.classList.add('is-authenticated');
        const fab = document.getElementById('sidebarFab');
        if (fab) {
            fab.removeAttribute('hidden');
        }
        const chatAreaEl = document.getElementById('chatArea');
        if (chatAreaEl) chatAreaEl.removeAttribute('hidden');

        const inboxRelayStatuses = await mergeOwnInboxRelays();
        setRelayStatusTooltip(relayResults, inboxRelayStatuses);

        // Live subscription first so new mail arrives while history is still decrypting.
        // History uses paginated querySync (relay result caps) + batched UI updates for mobile perf.
        subscribeToMessages();
        void fetchHistoricalGiftWraps();

    } catch (error) {
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
async function fetchKind10050Relays(authorPubkey) {
    try {
        const queryRelays = dmRelayUrls?.length ? dmRelayUrls : RELAY_URLS;
        const ev = await pool.get(queryRelays, { kinds: [10050], authors: [authorPubkey] });
        if (!ev?.tags?.length) return [];
        return ev.tags.filter((t) => t[0] === 'relay' && typeof t[1] === 'string' && t[1].length > 0).map((t) => t[1]);
    } catch (e) {
        console.warn('fetchKind10050Relays failed:', e);
        return [];
    }
}

/** @returns {Promise<Array<{ url: string, success: boolean }>>} */
async function mergeOwnInboxRelays() {
    const mine = await fetchKind10050Relays(publicKey);
    if (!mine.length) {
        dmRelayUrls = [...RELAY_URLS];
        return [];
    }
    dmRelayUrls = [...new Set([...RELAY_URLS, ...mine])];
    return Promise.all(
        mine.map(async (url) => {
            try {
                await pool.ensureRelay(url);
                return { url, success: true };
            } catch (err) {
                console.warn('Could not connect to inbox relay:', url, err);
                return { url, success: false };
            }
        })
    );
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

    const pageLimit = 500;
    const maxPages = 40;
    const maxWait = Math.min(65000, 20000 + dmRelayUrls.length * 6000);
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

            const events = await pool.querySync(dmRelayUrls, filter, { maxWait });
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

/** After bulk inbox load, fetch display names without blocking decrypt. */
function prefetchMissingConversationProfiles() {
    for (const pubkey of Object.keys(conversations)) {
        if (userProfiles[pubkey]) {
            continue;
        }
        void fetchUserProfile(pubkey).then(() => {
            updateConversationsList();
            if (currentChat === pubkey) {
                updateChatHeader(pubkey);
            }
        });
    }
}

function subscribeToMessages() {
    // Subscribe to kind 1059 (gift-wrapped) events tagged with our pubkey
    // SimplePool.subscribe automatically queries all connected relays
    // Store the subscription so it stays alive
    console.log('Setting up subscription for publicKey:', publicKey);
    console.log('Subscribing to relays:', dmRelayUrls);

    let eventCount = 0;

    // Create filter for gift-wrapped messages (kind 1059) tagged with our pubkey
    // Note: pool.subscribe takes a single filter object, not an array
    // Remove 'since' to get all historical messages, not just recent ones
    const filter = {
        kinds: [1059],
        '#p': [publicKey]
    };
    console.log('Subscription filter:', JSON.stringify(filter, null, 2));

    messageSubscription = pool.subscribe(dmRelayUrls, filter, {
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

    console.log('✅ Subscription active - listening for messages on', dmRelayUrls.length, 'relays');
    console.log('💡 Querying all historical messages (no time limit)');
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

        // Step 3: Decrypt the seal to get the rumor (kind 14)
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
        
        // Step 4: Verify it's a chat message (kind 14)
        if (rumor.kind !== 14) {
            console.error('Expected kind 14 rumor, got:', rumor.kind);
            return;
        }

        // Step 5: Verify the sender
        if (normalizePubkey(seal.pubkey) !== normalizePubkey(rumor.pubkey)) {
            console.error('Sender pubkey mismatch - potential impersonation attempt');
            return;
        }

        const authorPubkey = normalizePubkey(rumor.pubkey);
        // Peer thread key: incoming DMs use the author; our own messages (sender copy, kind 14
        // pubkey = us) must use the recipient from the rumor's p tag so they land in the same
        // conversation as openChat(peer) / sendMessage().
        let conversationPubkey = authorPubkey;
        if (authorPubkey === publicKey) {
            const pTag = Array.isArray(rumor.tags)
                ? rumor.tags.find((t) => t[0] === 'p' && typeof t[1] === 'string' && t[1].length)
                : null;
            if (!pTag) {
                console.error('Outgoing kind 14 missing p tag; cannot assign conversation');
                return;
            }
            conversationPubkey = normalizePubkey(pTag[1]);
        }

        if (!conversations[conversationPubkey]) {
            conversations[conversationPubkey] = [];
        }

        // Same logical message can appear locally first, then again from our self-addressed gift wrap
        if (rumor.id && conversations[conversationPubkey].some((m) => m.id === rumor.id)) {
            return;
        }

        conversations[conversationPubkey].push({
            id: rumor.id,
            content: rumor.content,
            timestamp: rumor.created_at,
            from: authorPubkey,
            actualTimestamp: giftWrap.created_at
        });

        conversations[conversationPubkey].sort((a, b) => a.timestamp - b.timestamp);

        if (!options.suppressUi) {
            updateConversationsList();
            if (currentChat === conversationPubkey) {
                displayMessages(conversationPubkey);
                updateChatHeader(conversationPubkey);
            }
            if (!userProfiles[conversationPubkey]) {
                void fetchUserProfile(conversationPubkey).then(() => {
                    updateConversationsList();
                    if (currentChat === conversationPubkey) {
                        updateChatHeader(conversationPubkey);
                    }
                });
            }
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

function updateConversationsList() {
    const list = document.getElementById('conversationsList');
    list.innerHTML = '';

    Object.keys(conversations)
        .sort((a, b) => lastConversationSortTime(conversations[b]) - lastConversationSortTime(conversations[a]))
        .forEach((pubkey) => {
            const conv = conversations[pubkey];
            const lastMsg = conv.length > 0 ? conv[conv.length - 1] : null;

            const item = document.createElement('div');
            item.className = 'conversation-item' + (currentChat === pubkey ? ' active' : '');
            item.onclick = () => openChat(pubkey);

            const displayName = getDisplayName(pubkey);
            const dateIndicator = lastMsg ? formatConversationDate(lastMsg.timestamp) : '';
            const preview = lastMsg
                ? `${lastMsg.content.substring(0, 50)}${lastMsg.content.length > 50 ? '...' : ''}`
                : 'No messages yet';

            item.innerHTML = `
            <div style="display: flex; justify-content: space-between; align-items: flex-start; margin-bottom: 4px;">
                <div class="conversation-pubkey">${displayName}</div>
                <div class="conversation-date">${dateIndicator}</div>
            </div>
            <div class="conversation-preview">${preview}</div>
        `;

            list.appendChild(item);
        });
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
}

function backToConversations() {
    setMobileChatPanel(false);
}

window.backToConversations = backToConversations;

// Update chat header with display name
function updateChatHeader(pubkey) {
    const displayName = getDisplayName(pubkey);
    const shortPubkey = pubkey.slice(0, 16) + '...' + pubkey.slice(-16);
    
    // Show display name, or short pubkey if no name available
    const profile = userProfiles[pubkey];
    if (profile && (profile.display_name || profile.name)) {
        document.getElementById('currentChatPubkey').textContent = displayName;
    } else {
        document.getElementById('currentChatPubkey').textContent = shortPubkey;
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
        bodyEl.textContent = msg.content;

        const timeEl = document.createElement('div');
        timeEl.className = 'message-time';
        timeEl.textContent = formatTimestamp(msg.timestamp);

        div.appendChild(bodyEl);
        div.appendChild(timeEl);

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

async function sendMessage() {
    const input = document.getElementById('messageInput');
    const sendBtn = document.getElementById('sendBtn');
    const content = input.value.trim();

    if (!content || !currentChat) return;

    sendBtn.disabled = true;
    sendBtn.innerHTML = '<div class="loading"></div>';

    try {
        const now = Math.floor(Date.now() / 1000);

        const recipientInboxRelays = await fetchKind10050Relays(currentChat);
        const publishRelays =
            recipientInboxRelays.length > 0
                ? [...new Set([...recipientInboxRelays, ...RELAY_URLS])]
                : [...RELAY_URLS];
        const relayHint = recipientInboxRelays[0] || null;

        // Step 1: Create the rumor (kind 14) — unsigned; NIP-17 requires id + created_at (same as nostr-tools createRumor)
        const rumor = {
            kind: 14,
            pubkey: publicKey,
            created_at: now,
            tags: relayHint ? [['p', currentChat, relayHint]] : [['p', currentChat]],
            content: content
        };
        rumor.id = getEventHash(rumor);

        // Step 2: Seal the rumor (kind 13)
        const sealContent = JSON.stringify(rumor);
        // Use extension's nip44 (we already checked it exists at connection time)
        const encryptedRumor = await window.nostr.nip44.encrypt(currentChat, sealContent);

        // p tag = DM counterparty for NIP-44. Required so when we reload, decrypt(..., seal) uses the
        // recipient (encrypt was nip44.encrypt(currentChat, …), not encrypt(self, …)).
        const sealTemplate = {
            kind: 13,
            pubkey: publicKey,
            created_at: getRandomPastTimestamp(),
            tags: relayHint ? [['p', currentChat, relayHint]] : [['p', currentChat]],
            content: encryptedRumor
        };

        const signedSeal = await window.nostr.signEvent(sealTemplate);
        // Use the signer output but keep our ciphertext/tags if the extension omits them
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

        // Step 3: Gift wrap for recipient (publish to their inbox relays per NIP-17 + defaults)
        await createAndPublishGiftWrap(sealToWrap, currentChat, publishRelays, relayHint);

        // Step 4: Gift wrap for sender (ourselves) — use our inbox + defaults so our other clients see the same thread
        const selfInbox = await fetchKind10050Relays(publicKey);
        const selfPublishRelays =
            selfInbox.length > 0 ? [...new Set([...selfInbox, ...RELAY_URLS])] : publishRelays;
        // Sender copy: only use our own inbox relay hint, not the peer's (avoids wrong room on our other clients)
        await createAndPublishGiftWrap(sealToWrap, publicKey, selfPublishRelays, selfInbox[0] || null);

        // Add to local conversation
        if (!conversations[currentChat]) {
            conversations[currentChat] = [];
        }

        conversations[currentChat].push({
            id: rumor.id,
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

async function createAndPublishGiftWrap(seal, recipientPubkey, publishRelays, relayHint) {
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
        // If all relays fail, log but don't throw - we still want to show the message locally
        console.warn('Failed to publish gift wrap to all relays:', error);
        // Don't throw - allow the message to appear locally even if publish fails
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
});

