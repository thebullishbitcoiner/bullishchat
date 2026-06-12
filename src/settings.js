import * as nip19 from 'nostr-tools/nip19';

import { state } from './state.js';
import {
    normalizePubkey,
    RELAY_URLS,
    DEFAULT_QUICK_REACTIONS,
    DEFAULT_EXTRA_REACTIONS,
    MAX_CUSTOM_REACTION_EMOJIS,
    CUSTOM_REACTION_SET_KIND,
    CUSTOM_REACTION_SET_D_TAG,
    EMOJI_DISCOVERY_PAGE_LIMIT,
    EMOJI_DISCOVERY_MAX_PAGES,
    DEFAULT_BLOSSOM_SERVERS,
    BLOSSOM_SERVER_LIST_KIND
} from './constants.js';
import { idbPut } from './db.js';
import { nostrAuthHandler, sortRelaysForRead, fetchKind10050Relays, fetchKind10063Servers } from './relay.js';
import { getDisplayName, enrichDiscoverEmojiSetAuthors } from './profile.js';
import {
    normalizeCustomEmojiLines,
    emojiShortcodeFromToken,
    getTagValue,
    syncBodyOverlayLock,
    displayMessages
} from './ui.js';
import { updateSettingsSyncUiState, runManualInboxSyncNow, logSyncTelemetrySnapshot } from './sync.js';

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

export function renderSettingsRelayList() {
    const list = document.getElementById('settingsRelayList');
    if (!list) return;
    list.innerHTML = '';
    if (!state.settingsRelayDraft.length) {
        list.innerHTML = '<div class="new-chat-suggestion-empty" role="status">No DM relays configured yet.</div>';
        return;
    }
    for (const relay of state.settingsRelayDraft) {
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
            state.settingsRelayDraft = state.settingsRelayDraft.filter((r) => r !== relay);
            renderSettingsRelayList();
        });
        row.appendChild(text);
        row.appendChild(rm);
        list.appendChild(row);
    }
}

function normalizeBlossomUrl(raw) {
    const t = (raw || '').trim();
    if (!t) return null;
    let u;
    try {
        u = new URL(t);
    } catch {
        return null;
    }
    if (u.protocol !== 'https:') return null;
    u.hash = '';
    u.search = '';
    return u.toString().replace(/\/$/, '');
}

export function renderSettingsBlossomList() {
    const list = document.getElementById('settingsBlossomList');
    if (!list) return;
    list.innerHTML = '';
    if (!state.settingsBlossomDraft.length) {
        list.innerHTML = '<div class="new-chat-suggestion-empty" role="status">No Blossom servers configured yet.</div>';
        return;
    }
    for (const server of state.settingsBlossomDraft) {
        const row = document.createElement('div');
        row.className = 'settings-relay-item';
        const text = document.createElement('div');
        text.className = 'settings-relay-url';
        text.textContent = server;
        text.title = server;
        const rm = document.createElement('button');
        rm.type = 'button';
        rm.className = 'settings-relay-remove';
        rm.setAttribute('aria-label', `Remove server ${server}`);
        rm.textContent = '×';
        rm.addEventListener('click', () => {
            state.settingsBlossomDraft = state.settingsBlossomDraft.filter((s) => s !== server);
            renderSettingsBlossomList();
        });
        row.appendChild(text);
        row.appendChild(rm);
        list.appendChild(row);
    }
}

export async function saveSettingsBlossomServers() {
    const status = document.getElementById('settingsBlossomStatus');
    const saveBtn = document.getElementById('settingsBlossomSaveBtn');
    if (!state.pool || !state.publicKey) {
        if (status) status.textContent = 'Connect first.';
        return;
    }
    if (!state.settingsBlossomDraft.length) {
        if (status) status.textContent = 'Add at least one server URL.';
        return;
    }
    if (saveBtn) saveBtn.disabled = true;
    if (status) status.textContent = 'Saving…';
    try {
        const ev = {
            kind: BLOSSOM_SERVER_LIST_KIND,
            created_at: Math.floor(Date.now() / 1000),
            tags: state.settingsBlossomDraft.map((url) => ['server', url]),
            content: ''
        };
        const signed = await window.nostr.signEvent(ev);
        const targets = [...new Set([...state.dmRelayUrls, ...RELAY_URLS])];
        const publishAttempts = targets.map(async (url) => {
            await state.pool.publish([url], signed, { onauth: nostrAuthHandler });
            return url;
        });
        await Promise.any(publishAttempts);
        state.blossomServers = [...new Set(state.settingsBlossomDraft)];
        void idbPut('meta', { key: 'blossomServers', value: state.blossomServers }).catch(() => {});
        if (status) status.textContent = `Saved ${state.settingsBlossomDraft.length} server(s) as kind ${BLOSSOM_SERVER_LIST_KIND}.`;
    } catch (err) {
        if (status) status.textContent = 'Could not publish settings. Try again.';
        console.error('Failed to save kind 10063 blossom servers:', err);
    } finally {
        if (saveBtn) saveBtn.disabled = false;
    }
}

export function currentEmojiEditorText() {
    const list = state.customReactionEmojiSet.length
        ? state.customReactionEmojiSet
        : [...DEFAULT_QUICK_REACTIONS, ...DEFAULT_EXTRA_REACTIONS];
    return list.join('\n');
}

export function pruneCustomReactionEmojiUrlMapToDraft() {
    const used = new Set();
    for (const t of state.settingsEmojiDraftSet) {
        const sc = emojiShortcodeFromToken(t);
        if (sc) used.add(sc);
    }
    const next = {};
    for (const key of Object.keys(state.customReactionEmojiUrlMap)) {
        if (used.has(key)) next[key] = state.customReactionEmojiUrlMap[key];
    }
    state.customReactionEmojiUrlMap = next;
}

export function removeEmojiFromDraftToken(token) {
    state.settingsEmojiDraftSet = state.settingsEmojiDraftSet.filter((t) => t !== token);
    pruneCustomReactionEmojiUrlMapToDraft();
    renderSettingsEmojiPreview(state.settingsEmojiDraftSet);
}

/** Append one reaction from a discovered set; existing URLs win for the same shortcode. */
export function addDiscoveredEmojiTokenToDraft(set, token) {
    const emojiStatus = document.getElementById('settingsEmojiStatus');
    if (state.settingsEmojiDraftSet.includes(token)) {
        if (emojiStatus) emojiStatus.textContent = 'That reaction is already in your set.';
        return false;
    }
    if (state.settingsEmojiDraftSet.length >= MAX_CUSTOM_REACTION_EMOJIS) {
        if (emojiStatus) {
            emojiStatus.textContent = `Your set is full (${MAX_CUSTOM_REACTION_EMOJIS}). Remove one in Reaction Emoji Set before adding more.`;
        }
        return false;
    }
    const merged = normalizeCustomEmojiLines([...state.settingsEmojiDraftSet, token].join('\n'));
    if (merged.length <= state.settingsEmojiDraftSet.length) {
        if (emojiStatus) emojiStatus.textContent = 'Could not add that reaction.';
        return false;
    }
    const sc = emojiShortcodeFromToken(token);
    if (sc && set.urlMap?.[sc]) {
        state.customReactionEmojiUrlMap = { [sc]: set.urlMap[sc], ...state.customReactionEmojiUrlMap };
    }
    state.settingsEmojiDraftSet = merged;
    pruneCustomReactionEmojiUrlMapToDraft();
    renderSettingsEmojiPreview(state.settingsEmojiDraftSet);
    if (emojiStatus) {
        emojiStatus.textContent = `Added a reaction from "${set.name}". Save to publish on Nostr.`;
    }
    return true;
}

export function populateSettingsEmojiTileItem(item, token, urlMap) {
    const shortcode = emojiShortcodeFromToken(token);
    const url = shortcode ? (urlMap[shortcode] || '') : '';
    if (url) {
        const img = document.createElement('img');
        img.src = url;
        img.alt = token;
        img.referrerPolicy = 'no-referrer';
        img.loading = 'lazy';
        item.appendChild(img);
    } else if (shortcode) {
        const miss = document.createElement('span');
        miss.className = 'settings-emoji-preview-missing';
        miss.textContent = '?';
        miss.title = 'No image URL for this reaction';
        item.appendChild(miss);
    } else {
        item.textContent = token;
    }
}

export function renderSettingsEmojiLoading() {
    const host = document.getElementById('settingsEmojiPreview');
    if (!host) return;
    host.innerHTML = '';
    const wrap = document.createElement('div');
    wrap.className = 'settings-emoji-loading';
    wrap.setAttribute('role', 'status');
    wrap.setAttribute('aria-busy', 'true');
    wrap.setAttribute('aria-live', 'polite');
    const spinner = document.createElement('span');
    spinner.className = 'settings-emoji-loading-spinner';
    spinner.setAttribute('aria-hidden', 'true');
    const msg = document.createElement('p');
    msg.className = 'settings-emoji-loading-msg';
    msg.textContent = 'Loading your emoji set from relays…';
    wrap.appendChild(spinner);
    wrap.appendChild(msg);
    host.appendChild(wrap);
}

export function renderSettingsEmojiPreview(emojis) {
    const host = document.getElementById('settingsEmojiPreview');
    if (!host) return;
    host.innerHTML = '';
    if (!emojis.length) {
        host.innerHTML = '<div class="new-chat-suggestion-empty" role="status">No emojis to preview.</div>';
        return;
    }
    const list = emojis.slice(0, MAX_CUSTOM_REACTION_EMOJIS);
    for (const token of list) {
        const chip = document.createElement('div');
        chip.className = 'settings-emoji-preview-chip';
        const item = document.createElement('div');
        item.className = 'settings-emoji-preview-item';
        populateSettingsEmojiTileItem(item, token, state.customReactionEmojiUrlMap);
        const rm = document.createElement('button');
        rm.type = 'button';
        rm.className = 'settings-emoji-preview-remove';
        rm.setAttribute('aria-label', `Remove ${token} from set`);
        rm.textContent = '×';
        rm.addEventListener('click', (e) => {
            e.preventDefault();
            e.stopPropagation();
            removeEmojiFromDraftToken(token);
        });
        chip.appendChild(item);
        chip.appendChild(rm);
        host.appendChild(chip);
    }
    if (emojis.length > MAX_CUSTOM_REACTION_EMOJIS) {
        const more = document.createElement('div');
        more.className = 'new-chat-suggestion-empty';
        more.style.gridColumn = '1 / -1';
        more.style.marginTop = '4px';
        more.textContent = `Showing first ${MAX_CUSTOM_REACTION_EMOJIS} of ${emojis.length}. Remove some to see the rest.`;
        host.appendChild(more);
    }
}

export async function openSettingsModal() {
    const modal = document.getElementById('settingsModal');
    const input = document.getElementById('settingsRelayInput');
    const status = document.getElementById('settingsRelayStatus');
    const emojiStatus = document.getElementById('settingsEmojiStatus');
    const discoverStatus = document.getElementById('settingsEmojiDiscoverStatus');
    if (!modal || !state.publicKey) return;
    modal.hidden = false;
    const collapsibles = modal.querySelectorAll('.settings-section');
    collapsibles.forEach((section) => {
        if (section instanceof HTMLDetailsElement) {
            section.open = false;
        }
    });
    syncBodyOverlayLock();
    renderSettingsEmojiLoading();
    if (emojiStatus) emojiStatus.textContent = 'Loading your emoji set…';
    await loadOwnCustomReactionSetFromNostr();
    state.settingsRelayDraft = await fetchKind10050Relays(state.publicKey);
    if (!state.settingsRelayDraft.length) {
        state.settingsRelayDraft = [...RELAY_URLS];
    }
    renderSettingsRelayList();
    if (status) {
        status.textContent = 'Edit your DM inbox relays and save to publish kind 10050.';
    }

    state.settingsBlossomDraft = await fetchKind10063Servers(state.publicKey);
    if (!state.settingsBlossomDraft.length) {
        state.settingsBlossomDraft = [...(state.blossomServers.length ? state.blossomServers : DEFAULT_BLOSSOM_SERVERS)];
    }
    renderSettingsBlossomList();
    const blossomStatus = document.getElementById('settingsBlossomStatus');
    if (blossomStatus) {
        blossomStatus.textContent = 'Edit your Blossom upload servers and save to publish kind 10063.';
    }
    if (input) {
        input.value = 'wss://';
        setTimeout(() => input.focus(), 30);
    }
    state.settingsEmojiDraftSet = state.customReactionEmojiSet.length
        ? [...state.customReactionEmojiSet]
        : [...DEFAULT_QUICK_REACTIONS, ...DEFAULT_EXTRA_REACTIONS];
    renderSettingsEmojiPreview(state.settingsEmojiDraftSet);
    if (emojiStatus) {
        emojiStatus.textContent = state.customReactionEmojiSet.length
            ? `Loaded ${state.customReactionEmojiSet.length} custom emojis from Nostr.`
            : 'No custom set on Nostr. Using default emoji set.';
    }
    if (discoverStatus) {
        discoverStatus.textContent = state.emojiDiscoverCatalog.length
            ? `${state.emojiDiscoverCatalog.length} set(s) cached. Discover relays were already queried this session.`
            : 'Expand Discover Emoji Sets once to query relays (runs once per app session).';
    }
    state.emojiDiscoverDetailSet = null;
    const discoverSearch = document.getElementById('settingsEmojiDiscoverSearch');
    if (discoverSearch) discoverSearch.value = '';
    renderDiscoveredEmojiSets();
    const syncStatus = document.getElementById('settingsSyncStatus');
    if (syncStatus && !state.manualInboxSyncInFlight) {
        syncStatus.textContent = '';
    }
    updateSettingsSyncUiState();
}

export function closeSettingsModal() {
    const modal = document.getElementById('settingsModal');
    if (modal) modal.hidden = true;
    syncBodyOverlayLock();
}

export async function saveSettingsRelays() {
    const status = document.getElementById('settingsRelayStatus');
    const saveBtn = document.getElementById('settingsSaveBtn');
    if (!state.pool || !state.publicKey) {
        if (status) status.textContent = 'Connect first.';
        return;
    }
    if (!state.settingsRelayDraft.length) {
        if (status) status.textContent = 'Add at least one relay URL.';
        return;
    }
    if (saveBtn) saveBtn.disabled = true;
    if (status) status.textContent = 'Saving…';
    try {
        const ev = {
            kind: 10050,
            created_at: Math.floor(Date.now() / 1000),
            tags: state.settingsRelayDraft.map((url) => ['relay', url]),
            content: ''
        };
        const signed = await window.nostr.signEvent(ev);
        const targets = [...new Set([...state.dmRelayUrls, ...RELAY_URLS, ...state.settingsRelayDraft])];
        const publishAttempts = targets.map(async (url) => {
            await state.pool.publish([url], signed, { onauth: nostrAuthHandler });
            return url;
        });
        await Promise.any(publishAttempts);
        state.dmRelayUrls = [...new Set(state.settingsRelayDraft)];
        void idbPut('meta', { key: 'dmRelayUrls', value: state.dmRelayUrls }).catch(() => {});
        if (status) status.textContent = `Saved ${state.settingsRelayDraft.length} relay(s).`;
    } catch (err) {
        if (status) status.textContent = 'Could not publish settings. Try again.';
        console.error('Failed to save kind 10050 relays:', err);
    } finally {
        if (saveBtn) saveBtn.disabled = false;
    }
}

export function initSettingsUi() {
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
    const emojiDiscoverSearch = document.getElementById('settingsEmojiDiscoverSearch');

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
            if (!state.settingsRelayDraft.includes(normalized)) {
                state.settingsRelayDraft.push(normalized);
                state.settingsRelayDraft = [...new Set(state.settingsRelayDraft)];
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

    const blossomAddBtn = document.getElementById('settingsBlossomAddBtn');
    const blossomInput = document.getElementById('settingsBlossomInput');
    const blossomSaveBtn = document.getElementById('settingsBlossomSaveBtn');
    const blossomStatus = document.getElementById('settingsBlossomStatus');
    if (blossomAddBtn && blossomInput) {
        blossomAddBtn.addEventListener('click', () => {
            const normalized = normalizeBlossomUrl(blossomInput.value);
            if (!normalized) {
                if (blossomStatus) blossomStatus.textContent = 'Enter a valid https:// server URL.';
                return;
            }
            if (!state.settingsBlossomDraft.includes(normalized)) {
                state.settingsBlossomDraft.push(normalized);
                state.settingsBlossomDraft = [...new Set(state.settingsBlossomDraft)];
                renderSettingsBlossomList();
                if (blossomStatus) blossomStatus.textContent = '';
            }
            blossomInput.value = 'https://';
            blossomInput.focus();
        });
        blossomInput.addEventListener('keydown', (e) => {
            if (e.key === 'Enter') {
                e.preventDefault();
                blossomAddBtn.click();
            }
        });
    }
    if (blossomSaveBtn) {
        blossomSaveBtn.addEventListener('click', () => {
            void saveSettingsBlossomServers();
        });
    }

    if (emojiSaveBtn) {
        emojiSaveBtn.addEventListener('click', async () => {
            const parsed = normalizeCustomEmojiLines(state.settingsEmojiDraftSet.join('\n'));
            if (parsed.length < 5) {
                if (emojiStatus) emojiStatus.textContent = 'Import a set with at least 5 emojis.';
                return;
            }
            emojiSaveBtn.disabled = true;
            if (emojiStatus) emojiStatus.textContent = 'Saving to Nostr…';
            try {
                await saveOwnCustomReactionSetToNostr(parsed);
                if (emojiStatus) emojiStatus.textContent = `Saved ${state.customReactionEmojiSet.length} custom emojis to Nostr.`;
                state.settingsEmojiDraftSet = [...state.customReactionEmojiSet];
                renderSettingsEmojiPreview(state.settingsEmojiDraftSet);
                if (state.currentChat) {
                    displayMessages(state.currentChat);
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
            state.settingsEmojiDraftSet = [...DEFAULT_QUICK_REACTIONS, ...DEFAULT_EXTRA_REACTIONS];
            renderSettingsEmojiPreview(state.settingsEmojiDraftSet);
            if (emojiStatus) emojiStatus.textContent = 'Reset to default emoji set (saved on Nostr).';
            if (state.currentChat) {
                displayMessages(state.currentChat);
            }
            emojiResetBtn.disabled = false;
        });
    }
    if (emojiDiscoverSearch) {
        emojiDiscoverSearch.addEventListener('input', () => {
            if (state.emojiDiscoverSearchDebounce) clearTimeout(state.emojiDiscoverSearchDebounce);
            state.emojiDiscoverSearchDebounce = setTimeout(() => {
                state.emojiDiscoverSearchDebounce = null;
                renderDiscoveredEmojiSets();
            }, 150);
        });
    }
    const emojiDiscoverSection = document.querySelector('.settings-section--emoji-discover');
    if (emojiDiscoverSection instanceof HTMLDetailsElement) {
        emojiDiscoverSection.addEventListener('toggle', () => {
            if (emojiDiscoverSection.open && !state.emojiDiscoverQueriedThisModalOpen) {
                state.emojiDiscoverQueriedThisModalOpen = true;
                void discoverEmojiSets();
            }
        });
    }
    const syncNowBtn = document.getElementById('settingsSyncNowBtn');
    const syncLogBtn = document.getElementById('settingsSyncLogBtn');
    if (syncNowBtn) {
        syncNowBtn.addEventListener('click', () => {
            void runManualInboxSyncNow();
        });
    }
    if (syncLogBtn) {
        syncLogBtn.addEventListener('click', () => {
            logSyncTelemetrySnapshot();
            const syncStatus = document.getElementById('settingsSyncStatus');
            if (syncStatus) {
                syncStatus.textContent = 'Stats logged to the browser console.';
            }
        });
    }
    updateSettingsSyncUiState();
}

export function parseCustomReactionSetEvent(ev) {
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

export function parseCustomReactionSetMeta(ev) {
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

export async function discoverEmojiSets() {
    const status = document.getElementById('settingsEmojiDiscoverStatus');
    const list = document.getElementById('settingsEmojiDiscoverList');
    if (!state.pool) {
        if (status) status.textContent = 'Connect first.';
        return;
    }
    if (state.emojiDiscoverInFlight) return;
    state.emojiDiscoverInFlight = true;
    state.emojiDiscoverDetailSet = null;
    renderEmojiDiscoverLoading(list);
    if (status) status.textContent = 'Loading public emoji sets from relays…';
    try {
        const relays = [...new Set([...(state.dmRelayUrls?.length ? state.dmRelayUrls : []), ...RELAY_URLS])];
        const ordered = sortRelaysForRead(relays);
        const newestByKey = new Map();
        let until;
        for (let page = 0; page < EMOJI_DISCOVERY_MAX_PAGES; page++) {
            const filter = { kinds: [CUSTOM_REACTION_SET_KIND], limit: EMOJI_DISCOVERY_PAGE_LIMIT };
            if (until !== undefined) filter.until = until;
            const maxWait = Math.min(65000, 12000 + ordered.length * 2000);
            const events = await state.pool.querySync(ordered, filter, { maxWait, onauth: nostrAuthHandler });
            const n = Array.isArray(events) ? events.length : 0;
            if (!n) break;
            for (const ev of events) {
                const d = getTagValue(ev.tags, 'd') || 'default';
                const key = `${normalizePubkey(ev.pubkey)}:${d}`;
                const prev = newestByKey.get(key);
                if (!prev || (ev.created_at || 0) > (prev.created_at || 0)) {
                    newestByKey.set(key, ev);
                }
            }
            events.sort((a, b) => (a.created_at || 0) - (b.created_at || 0));
            if (n < EMOJI_DISCOVERY_PAGE_LIMIT) break;
            until = (events[0].created_at || 0) - 1;
            if (until < 1) break;
        }
        const parsed = [];
        for (const ev of newestByKey.values()) {
            const parsedSet = parseCustomReactionSetMeta(ev);
            const emojis = parsedSet.emojis;
            if (!emojis.length) continue;
            const dTag = getTagValue(ev.tags, 'd') || 'default';
            const name =
                getTagValue(ev.tags, 'name') || getTagValue(ev.tags, 'title') || dTag || 'Untitled set';
            parsed.push({
                pubkey: normalizePubkey(ev.pubkey),
                dTag,
                name,
                emojis,
                urlMap: parsedSet.urlMap,
                count: emojis.length,
                createdAt: ev.created_at || 0
            });
        }
        parsed.sort((a, b) => b.createdAt - a.createdAt);
        state.emojiDiscoverCatalog = parsed;
        await enrichDiscoverEmojiSetAuthors(state.emojiDiscoverCatalog.map((s) => s.pubkey));
        syncEmojiDiscoverDetailFromCatalog();
        renderDiscoveredEmojiSets();
        if (status && !state.emojiDiscoverCatalog.length) {
            status.textContent = 'No parseable emoji sets found.';
        }
    } catch (e) {
        console.error('[emoji-discovery] query failed:', e);
        state.emojiDiscoverCatalog = [];
        state.emojiDiscoverDetailSet = null;
        renderDiscoveredEmojiSets();
        if (status) status.textContent = 'Could not discover emoji sets.';
    } finally {
        state.emojiDiscoverInFlight = false;
    }
}

export async function loadOwnCustomReactionSetFromNostr() {
    if (!state.pool || !state.publicKey) {
        state.customReactionEmojiSet = [];
        return;
    }
    try {
        const relays = [...new Set([...(state.dmRelayUrls?.length ? state.dmRelayUrls : []), ...RELAY_URLS])];
        const events = await state.pool.querySync(
            relays,
            {
                kinds: [CUSTOM_REACTION_SET_KIND],
                authors: [state.publicKey],
                '#d': [CUSTOM_REACTION_SET_D_TAG],
                limit: 5
            },
            { maxWait: 9000, onauth: nostrAuthHandler }
        );
        const newest = (events || []).sort((a, b) => (b.created_at || 0) - (a.created_at || 0))[0];
        const parsedSet = parseCustomReactionSetMeta(newest);
        state.customReactionEmojiSet = parsedSet.emojis;
        state.customReactionEmojiUrlMap = parsedSet.urlMap;
    } catch (e) {
        console.warn('Could not load custom reaction set from Nostr:', e);
        state.customReactionEmojiSet = [];
        state.customReactionEmojiUrlMap = {};
    }
}

export async function saveOwnCustomReactionSetToNostr(list) {
    if (!state.pool || !state.publicKey) {
        throw new Error('Connect first.');
    }
    const emojis = normalizeCustomEmojiLines((list || []).join('\n'));
    const emojiTags = [];
    const publishedUrlMap = {};
    for (const token of emojis) {
        const shortcode = emojiShortcodeFromToken(token);
        if (!shortcode) continue;
        const url = state.customReactionEmojiUrlMap[shortcode];
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
    const targets = [...new Set([...(state.dmRelayUrls?.length ? state.dmRelayUrls : []), ...RELAY_URLS])];
    const publishAttempts = targets.map(async (url) => {
        await state.pool.publish([url], signed, { onauth: nostrAuthHandler });
        return url;
    });
    await Promise.any(publishAttempts);
    state.customReactionEmojiSet = emojis;
    state.customReactionEmojiUrlMap = publishedUrlMap;
}

export function renderEmojiDiscoverDetailPanel(listEl, status) {
    const set = state.emojiDiscoverDetailSet;
    if (!set) return;
    const wrap = document.createElement('div');
    wrap.className = 'settings-emoji-discover-detail';

    const backRow = document.createElement('div');
    backRow.className = 'settings-emoji-discover-detail-bar';
    const back = document.createElement('button');
    back.type = 'button';
    back.className = 'settings-add-btn settings-emoji-discover-back-btn';
    back.textContent = '← All sets';
    back.addEventListener('click', () => {
        state.emojiDiscoverDetailSet = null;
        renderDiscoveredEmojiSets();
    });
    backRow.appendChild(back);
    wrap.appendChild(backRow);

    const head = document.createElement('div');
    head.className = 'settings-emoji-discover-detail-head';
    const title = document.createElement('div');
    title.className = 'settings-emoji-set-name';
    title.textContent = set.name;
    const sub = document.createElement('div');
    sub.className = 'settings-emoji-set-meta';
    const emojiLabel = set.count === 1 ? 'emoji' : 'emojis';
    sub.textContent = `${set.count} ${emojiLabel} · by ${getDisplayName(set.pubkey)}`;
    head.appendChild(title);
    head.appendChild(sub);
    wrap.appendChild(head);

    const grid = document.createElement('div');
    grid.className = 'settings-emoji-discover-detail-grid';
    const urlMap = set.urlMap || {};
    for (const token of set.emojis) {
        const chip = document.createElement('div');
        chip.className = 'settings-emoji-preview-chip';
        const item = document.createElement('div');
        item.className = 'settings-emoji-preview-item';
        populateSettingsEmojiTileItem(item, token, urlMap);
        const addBtn = document.createElement('button');
        addBtn.type = 'button';
        addBtn.className = 'settings-emoji-preview-add';
        addBtn.textContent = '+';
        const inDraft = state.settingsEmojiDraftSet.includes(token);
        if (inDraft) {
            addBtn.disabled = true;
            addBtn.setAttribute('aria-label', 'Already in your reaction set');
        } else {
            addBtn.setAttribute('aria-label', 'Add reaction to your set');
            addBtn.addEventListener('click', () => {
                if (addDiscoveredEmojiTokenToDraft(set, token)) {
                    renderDiscoveredEmojiSets();
                }
            });
        }
        chip.appendChild(item);
        chip.appendChild(addBtn);
        grid.appendChild(chip);
    }
    wrap.appendChild(grid);
    listEl.appendChild(wrap);
    if (status) {
        status.textContent = `Browsing "${set.name}". Add reactions one at a time.`;
    }
}

export function renderDiscoveredEmojiSets() {
    const list = document.getElementById('settingsEmojiDiscoverList');
    const status = document.getElementById('settingsEmojiDiscoverStatus');
    if (!list) return;
    list.innerHTML = '';
    if (!state.emojiDiscoverCatalog.length) {
        state.emojiDiscoverDetailSet = null;
        list.innerHTML = '<div class="new-chat-suggestion-empty" role="status">No emoji sets found on connected relays.</div>';
        return;
    }
    syncEmojiDiscoverDetailFromCatalog();
    if (state.emojiDiscoverDetailSet) {
        renderEmojiDiscoverDetailPanel(list, status);
        return;
    }
    const rows = getFilteredEmojiDiscoverRows();
    if (!rows.length) {
        list.innerHTML = '<div class="new-chat-suggestion-empty" role="status">No sets match your search.</div>';
        if (status) status.textContent = `${state.emojiDiscoverCatalog.length} set(s); none match filter.`;
        return;
    }
    if (status) {
        const q = getEmojiDiscoverFilterQuery();
        status.textContent = q
            ? `Showing ${rows.length} of ${state.emojiDiscoverCatalog.length} (filtered).`
            : `${state.emojiDiscoverCatalog.length} set(s) loaded.`;
    }
    for (const set of rows) {
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
        const previewTokens = set.emojis.slice(0, 4);
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

        const browseBtn = document.createElement('button');
        browseBtn.type = 'button';
        browseBtn.className = 'settings-add-btn';
        browseBtn.textContent = 'Open';
        browseBtn.addEventListener('click', () => {
            state.emojiDiscoverDetailSet = set;
            renderDiscoveredEmojiSets();
        });

        row.appendChild(main);
        row.appendChild(browseBtn);
        list.appendChild(row);
    }
}

export function renderEmojiDiscoverLoading(listEl) {
    if (!listEl) return;
    listEl.innerHTML = '';
    const wrap = document.createElement('div');
    wrap.className = 'settings-emoji-discover-loading';
    wrap.setAttribute('role', 'status');
    wrap.setAttribute('aria-busy', 'true');
    wrap.setAttribute('aria-live', 'polite');
    const spinner = document.createElement('span');
    spinner.className = 'settings-emoji-discover-spinner';
    spinner.setAttribute('aria-hidden', 'true');
    const msg = document.createElement('p');
    msg.className = 'settings-emoji-discover-loading-msg';
    msg.textContent = 'Loading public emoji sets from your relays…';
    wrap.appendChild(spinner);
    wrap.appendChild(msg);
    listEl.appendChild(wrap);
}

export function getEmojiDiscoverFilterQuery() {
    const el = document.getElementById('settingsEmojiDiscoverSearch');
    return (el?.value || '').trim();
}

export function tryDecodeNpubForDiscoverFilter(raw) {
    const s = (raw || '').trim();
    if (!s.toLowerCase().startsWith('npub')) return '';
    try {
        const dec = nip19.decode(s);
        if (dec.type === 'npub') return normalizePubkey(dec.data);
    } catch {
        /* ignore malformed bech32 */
    }
    return '';
}

export function matchesEmojiDiscoverFilter(set, qRaw) {
    const q = qRaw.toLowerCase();
    if (!q) return true;
    const pk = normalizePubkey(set.pubkey || '');
    const hexCandidate = q.replace(/\s/g, '');
    if (hexCandidate.length === 64 && /^[0-9a-f]+$/i.test(hexCandidate)) {
        if (pk === normalizePubkey(hexCandidate)) return true;
    }
    const npubPk = tryDecodeNpubForDiscoverFilter(qRaw);
    if (npubPk && pk === npubPk) return true;
    const name = (set.name || '').toLowerCase();
    const d = (set.dTag || '').toLowerCase();
    const disp = (getDisplayName(set.pubkey) || '').toLowerCase();
    return name.includes(q) || d.includes(q) || pk.toLowerCase().includes(q) || disp.includes(q);
}

export function getFilteredEmojiDiscoverRows() {
    const qRaw = getEmojiDiscoverFilterQuery();
    if (!qRaw) return state.emojiDiscoverCatalog;
    return state.emojiDiscoverCatalog.filter((set) => matchesEmojiDiscoverFilter(set, qRaw));
}

export function discoverSetKey(set) {
    return `${set.pubkey}:${set.dTag || 'default'}`;
}

export function syncEmojiDiscoverDetailFromCatalog() {
    if (!state.emojiDiscoverDetailSet) return;
    if (!state.emojiDiscoverCatalog.length) {
        state.emojiDiscoverDetailSet = null;
        return;
    }
    const k = discoverSetKey(state.emojiDiscoverDetailSet);
    const found = state.emojiDiscoverCatalog.find((s) => discoverSetKey(s) === k);
    state.emojiDiscoverDetailSet = found || null;
    if (!state.emojiDiscoverDetailSet) return;
    const qRaw = getEmojiDiscoverFilterQuery();
    if (qRaw && !matchesEmojiDiscoverFilter(state.emojiDiscoverDetailSet, qRaw)) {
        state.emojiDiscoverDetailSet = null;
    }
}
