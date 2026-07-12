import * as nip19 from 'nostr-tools/nip19';

import { state } from './state.js';
import {
    normalizePubkey,
    RELAY_URLS,
    DEFAULT_QUICK_REACTIONS,
    DEFAULT_EXTRA_REACTIONS,
    MAX_CUSTOM_REACTION_EMOJIS,
    CUSTOM_REACTION_SET_KIND,
    USER_EMOJI_LIST_KIND,
    EMOJI_DISCOVERY_PAGE_LIMIT,
    EMOJI_DISCOVERY_MAX_PAGES,
    DEFAULT_BLOSSOM_SERVERS,
    BLOSSOM_SERVER_LIST_KIND
} from './constants.js';
import { idbPut } from './db.js';
import { nostrAuthHandler, sortRelaysForRead, fetchKind10050Relays, fetchKind10063Servers } from './relay.js';
import { getDisplayName, fetchUserProfile, enrichDiscoverEmojiSetAuthors } from './profile.js';
import {
    normalizeCustomEmojiLines,
    emojiShortcodeFromToken,
    getTagValue,
    syncBodyOverlayLock,
    displayMessages,
    createAvatarNode
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
        text.textContent = relay.replace(/\/$/, '');
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

export function renderSettingsMutedList() {
    const list = document.getElementById('settingsMutedList');
    if (!list) return;
    list.innerHTML = '';
    if (!state.mutedPubkeys.size) {
        list.innerHTML = '<div class="new-chat-suggestion-empty" role="status">No muted users.</div>';
        return;
    }
    for (const pubkey of state.mutedPubkeys) {
        const row = document.createElement('div');
        row.className = 'settings-relay-item settings-muted-item';
        const avatar = createAvatarNode(pubkey, 'avatar settings-muted-avatar');
        row.appendChild(avatar);
        const text = document.createElement('div');
        text.className = 'settings-relay-url';
        text.textContent = getDisplayName(pubkey);
        text.title = pubkey;
        const rm = document.createElement('button');
        rm.type = 'button';
        rm.className = 'settings-relay-remove';
        rm.setAttribute('aria-label', `Unmute ${getDisplayName(pubkey)}`);
        rm.textContent = '×';
        rm.addEventListener('click', async () => {
            rm.disabled = true;
            const { unmuteConversation } = await import('./mute.js');
            await unmuteConversation(pubkey);
            renderSettingsMutedList();
            const status = document.getElementById('settingsMutedStatus');
            if (status) status.textContent = 'Unmuted.';
        });
        row.appendChild(text);
        row.appendChild(rm);
        list.appendChild(row);

        if (!state.userProfiles[pubkey]) {
            void fetchUserProfile(pubkey).then(() => renderSettingsMutedList());
        }
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
        const foreignTags = (state.ownKind10063Event?.tags || []).filter((t) => t[0] !== 'server');
        const ev = {
            kind: BLOSSOM_SERVER_LIST_KIND,
            created_at: Math.floor(Date.now() / 1000),
            tags: [...foreignTags, ...state.settingsBlossomDraft.map((url) => ['server', url])],
            content: state.ownKind10063Event?.content || ''
        };
        const signed = await window.nostr.signEvent(ev);
        const targets = [...new Set([...state.dmRelayUrls, ...RELAY_URLS])];
        const publishAttempts = targets.map(async (url) => {
            await state.pool.publish([url], signed, { onauth: nostrAuthHandler });
            return url;
        });
        await Promise.any(publishAttempts);
        state.ownKind10063Event = signed;
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

const SETTINGS_SECTION_TITLES = {
    relays: 'DM Inbox Relays',
    blossom: 'Blossom Upload Servers',
    muted: 'Muted Users',
    emoji: 'My Emojis',
    discover: 'Discover Emoji Sets',
    sync: 'Inbox Sync'
};

let activeSettingsSection = null;

export function openSettingsPage() {
    const page = document.getElementById('settingsPage');
    if (!page || !state.publicKey) return;
    page.hidden = false;
    // Discover's add-to-set flow edits this draft even if the My Emojis page was never opened.
    state.settingsEmojiDraftSet = state.customReactionEmojiSet.length
        ? [...state.customReactionEmojiSet]
        : [...DEFAULT_QUICK_REACTIONS, ...DEFAULT_EXTRA_REACTIONS];
    showSettingsSection(null);
    syncBodyOverlayLock();
}

export function closeSettingsPage() {
    const page = document.getElementById('settingsPage');
    if (page) page.hidden = true;
    activeSettingsSection = null;
    syncBodyOverlayLock();
}

/** Back one level: section page → menu, menu → close settings. */
export function settingsPageBack() {
    if (activeSettingsSection) {
        showSettingsSection(null);
    } else {
        closeSettingsPage();
    }
}

export function showSettingsSection(name) {
    activeSettingsSection = name;
    const menu = document.getElementById('settingsMenu');
    if (menu) menu.hidden = Boolean(name);
    document.querySelectorAll('.settings-subpage').forEach((el) => {
        el.hidden = el.id !== `settingsSubpage-${name}`;
    });
    const title = document.getElementById('settingsPageTitle');
    if (title) title.textContent = name ? SETTINGS_SECTION_TITLES[name] : 'Settings';
    const scroll = document.querySelector('.settings-page-scroll');
    if (scroll) scroll.scrollTop = 0;

    if (name === 'relays') void loadSettingsRelaysSection();
    else if (name === 'blossom') void loadSettingsBlossomSection();
    else if (name === 'muted') void loadSettingsMutedSection();
    else if (name === 'emoji') void loadSettingsEmojiSection();
    else if (name === 'discover') loadSettingsDiscoverSection();
    else if (name === 'sync') loadSettingsSyncSection();
}

async function loadSettingsRelaysSection() {
    const input = document.getElementById('settingsRelayInput');
    const status = document.getElementById('settingsRelayStatus');
    const list = document.getElementById('settingsRelayList');
    if (input) input.value = 'wss://';
    if (status) status.textContent = '';
    if (list) list.innerHTML = '<div class="new-chat-suggestion-empty" role="status">Loading relays…</div>';
    state.settingsRelayDraft = await fetchKind10050Relays(state.publicKey);
    if (!state.settingsRelayDraft.length) {
        state.settingsRelayDraft = [...RELAY_URLS];
    }
    if (activeSettingsSection !== 'relays') return;
    renderSettingsRelayList();
    if (status) status.textContent = 'Edit your DM inbox relays and save to publish kind 10050.';
}

async function loadSettingsBlossomSection() {
    const input = document.getElementById('settingsBlossomInput');
    const status = document.getElementById('settingsBlossomStatus');
    const list = document.getElementById('settingsBlossomList');
    if (input) input.value = 'https://';
    if (status) status.textContent = '';
    if (list) list.innerHTML = '<div class="new-chat-suggestion-empty" role="status">Loading servers…</div>';
    state.settingsBlossomDraft = await fetchKind10063Servers(state.publicKey);
    if (!state.settingsBlossomDraft.length) {
        state.settingsBlossomDraft = [...(state.blossomServers.length ? state.blossomServers : DEFAULT_BLOSSOM_SERVERS)];
    }
    if (activeSettingsSection !== 'blossom') return;
    renderSettingsBlossomList();
    if (status) status.textContent = 'Edit your Blossom upload servers and save to publish kind 10063.';
}

async function loadSettingsMutedSection() {
    // Render the cached list immediately, then refresh from relays so edits merge
    // against the newest event (mutes may have been added from another client).
    renderSettingsMutedList();
    const status = document.getElementById('settingsMutedStatus');
    if (status) status.textContent = 'Checking relays for updates…';
    const { loadMuteListFromNostr } = await import('./mute.js');
    await loadMuteListFromNostr();
    if (activeSettingsSection !== 'muted') return;
    renderSettingsMutedList();
    if (status) status.textContent = '';
}

async function loadSettingsEmojiSection() {
    const emojiStatus = document.getElementById('settingsEmojiStatus');
    renderSettingsEmojiLoading();
    if (emojiStatus) emojiStatus.textContent = 'Loading your emoji set…';
    await loadOwnCustomReactionSetFromNostr();
    if (activeSettingsSection !== 'emoji') return;
    state.settingsEmojiDraftSet = state.customReactionEmojiSet.length
        ? [...state.customReactionEmojiSet]
        : [...DEFAULT_QUICK_REACTIONS, ...DEFAULT_EXTRA_REACTIONS];
    renderSettingsEmojiPreview(state.settingsEmojiDraftSet);
    if (emojiStatus) {
        emojiStatus.textContent = state.customReactionEmojiSet.length
            ? `Loaded ${state.customReactionEmojiSet.length} custom emojis from Nostr.`
            : 'No custom set on Nostr. Using default emoji set.';
    }
}

function loadSettingsDiscoverSection() {
    const discoverStatus = document.getElementById('settingsEmojiDiscoverStatus');
    const discoverSearch = document.getElementById('settingsEmojiDiscoverSearch');
    state.emojiDiscoverDetailSet = null;
    if (discoverSearch) discoverSearch.value = '';
    if (!state.emojiDiscoverQueriedThisModalOpen) {
        state.emojiDiscoverQueriedThisModalOpen = true;
        void discoverEmojiSets();
        return;
    }
    renderDiscoveredEmojiSets();
    if (discoverStatus) {
        discoverStatus.textContent = state.emojiDiscoverCatalog.length
            ? `${state.emojiDiscoverCatalog.length} set(s) cached from earlier this session.`
            : 'No emoji sets found earlier this session.';
    }
}

function loadSettingsSyncSection() {
    const syncStatus = document.getElementById('settingsSyncStatus');
    if (syncStatus && !state.manualInboxSyncInFlight) {
        syncStatus.textContent = '';
    }
    updateSettingsSyncUiState();
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
        // Carry over anything another client put in the event that isn't the relay list itself.
        const foreignTags = (state.ownKind10050Event?.tags || []).filter((t) => t[0] !== 'relay');
        const ev = {
            kind: 10050,
            created_at: Math.floor(Date.now() / 1000),
            tags: [...foreignTags, ...state.settingsRelayDraft.map((url) => ['relay', url])],
            content: state.ownKind10050Event?.content || ''
        };
        const signed = await window.nostr.signEvent(ev);
        const targets = [...new Set([...state.dmRelayUrls, ...RELAY_URLS, ...state.settingsRelayDraft])];
        const publishAttempts = targets.map(async (url) => {
            await state.pool.publish([url], signed, { onauth: nostrAuthHandler });
            return url;
        });
        await Promise.any(publishAttempts);
        state.ownKind10050Event = signed;
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
    const backBtn = document.getElementById('settingsBackBtn');
    const menu = document.getElementById('settingsMenu');
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
            openSettingsPage();
        });
    }
    if (backBtn) {
        backBtn.addEventListener('click', settingsPageBack);
    }
    if (menu) {
        menu.addEventListener('click', (e) => {
            const item = e.target.closest('[data-settings-section]');
            if (item) showSettingsSection(item.dataset.settingsSection);
        });
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

/** Appends unseen tokens from extra into base; base's order and URLs win on conflict. */
function mergeEmojiMeta(base, extra) {
    const seen = new Set(base.emojis);
    for (const token of extra.emojis) {
        if (!seen.has(token)) {
            base.emojis.push(token);
            seen.add(token);
        }
    }
    base.urlMap = { ...extra.urlMap, ...base.urlMap };
}

/** 'a' tags pointing at kind 30030 emoji sets, from either the public tags or the private items. */
function extractEmojiSetRefs(tagList) {
    return (Array.isArray(tagList) ? tagList : [])
        .filter((t) => Array.isArray(t) && t[0] === 'a' && typeof t[1] === 'string' && t[1].startsWith(`${CUSTOM_REACTION_SET_KIND}:`))
        .map((t) => {
            const [, pk, ...rest] = t[1].split(':');
            return { pubkey: normalizePubkey(pk), d: rest.join(':') };
        })
        .filter((r) => r.pubkey);
}

export async function loadOwnCustomReactionSetFromNostr() {
    if (!state.pool || !state.publicKey) {
        state.customReactionEmojiSet = [];
        return;
    }
    try {
        const relays = [...new Set([...(state.dmRelayUrls?.length ? state.dmRelayUrls : []), ...RELAY_URLS])];
        const newestOf = (evs) => (evs || []).sort((a, b) => (b.created_at || 0) - (a.created_at || 0))[0];
        const emojiListEvents = await state.pool.querySync(
            relays,
            { kinds: [USER_EMOJI_LIST_KIND], authors: [state.publicKey], limit: 5 },
            { maxWait: 9000, onauth: nostrAuthHandler }
        );

        const merged = { emojis: [], urlMap: {} };

        // NIP-51 kind 10030 user emoji list: public + private emoji entries, then any
        // referenced kind 30030 sets ('a' tags in either half).
        const emojiList = newestOf(emojiListEvents);
        state.ownKind10030Event = emojiList || null;
        state.ownKind10030PrivateItems = [];
        state.ownKind10030ContentUnreadable = false;
        if (emojiList) {
            // Only merge tag-derived entries — the content-fallback parser would turn
            // an encrypted private list into garbage tokens.
            if ((emojiList.tags || []).some((t) => t[0] === 'emoji')) {
                mergeEmojiMeta(merged, parseCustomReactionSetMeta(emojiList));
            }

            // Private half: a JSON tag-array encrypted to self (NIP-44, or legacy NIP-04
            // detected by its '?iv=' suffix).
            if (emojiList.content) {
                try {
                    const decrypted = emojiList.content.includes('?iv=') && window.nostr?.nip04?.decrypt
                        ? await window.nostr.nip04.decrypt(state.publicKey, emojiList.content)
                        : await window.nostr.nip44.decrypt(state.publicKey, emojiList.content);
                    const parsed = JSON.parse(decrypted);
                    if (Array.isArray(parsed)) {
                        state.ownKind10030PrivateItems = parsed;
                        mergeEmojiMeta(merged, parseCustomReactionSetMeta({ tags: parsed, content: '' }));
                    } else {
                        state.ownKind10030ContentUnreadable = true;
                    }
                } catch (e) {
                    state.ownKind10030ContentUnreadable = true;
                    console.warn('Emoji list (kind 10030) content could not be decrypted — private entries will be preserved verbatim:', e);
                }
            }

            const seenRefs = new Set();
            const refs = [
                ...extractEmojiSetRefs(emojiList.tags),
                ...extractEmojiSetRefs(state.ownKind10030PrivateItems)
            ].filter((r) => {
                const key = `${r.pubkey}:${r.d}`;
                if (seenRefs.has(key)) return false;
                seenRefs.add(key);
                return true;
            });

            console.info(
                `Emoji list (kind 10030): ${(emojiList.tags || []).filter((t) => t[0] === 'emoji').length} public emoji tag(s), ` +
                `${state.ownKind10030PrivateItems.filter((t) => t[0] === 'emoji').length} private emoji item(s), ${refs.length} set ref(s); ` +
                `content: ${!emojiList.content ? 'none' : state.ownKind10030ContentUnreadable ? 'unreadable' : emojiList.content.includes('?iv=') ? 'nip04' : 'nip44'}`
            );

            if (refs.length) {
                const refEvents = await state.pool.querySync(
                    relays,
                    {
                        kinds: [CUSTOM_REACTION_SET_KIND],
                        authors: [...new Set(refs.map((r) => r.pubkey))],
                        '#d': [...new Set(refs.map((r) => r.d))],
                        limit: Math.min(refs.length * 4, 100)
                    },
                    { maxWait: 9000, onauth: nostrAuthHandler }
                );
                for (const ref of refs) {
                    const ev = (refEvents || [])
                        .filter((e) => normalizePubkey(e.pubkey) === ref.pubkey && getTagValue(e.tags, 'd') === ref.d)
                        .sort((a, b) => (b.created_at || 0) - (a.created_at || 0))[0];
                    if (ev) mergeEmojiMeta(merged, parseCustomReactionSetMeta(ev));
                }
            }
        }

        merged.emojis = normalizeCustomEmojiLines(merged.emojis.join('\n'));
        state.customReactionEmojiSet = merged.emojis;
        state.customReactionEmojiUrlMap = merged.urlMap;
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
    if (emojis.length && !emojiTags.length) {
        throw new Error('No NIP-30 emoji tag entries available to publish.');
    }

    // NIP-51 kind 10030: each entry goes back to the half it came from. New entries
    // follow the list's existing style (private if the other client kept them private).
    // 'a' set refs, other tags, and non-emoji private items are carried over verbatim.
    const canEditPrivate = !state.ownKind10030ContentUnreadable;
    const priorPrivateItems = state.ownKind10030PrivateItems || [];
    const privateShortcodes = new Set(
        priorPrivateItems.filter((t) => Array.isArray(t) && t[0] === 'emoji').map((t) => t[1])
    );
    const preferPrivate = canEditPrivate && privateShortcodes.size > 0;

    const privateEmojiTags = [];
    const publicEmojiTags = [];
    for (const tag of emojiTags) {
        if (canEditPrivate && (privateShortcodes.has(tag[1]) || preferPrivate)) {
            privateEmojiTags.push(tag);
        } else {
            publicEmojiTags.push(tag);
        }
    }

    const foreignTags = (state.ownKind10030Event?.tags || []).filter((t) => t[0] !== 'emoji');
    let content = state.ownKind10030Event?.content || '';
    let newPrivateItems = priorPrivateItems;
    if (canEditPrivate) {
        newPrivateItems = [
            ...priorPrivateItems.filter((t) => !(Array.isArray(t) && t[0] === 'emoji')),
            ...privateEmojiTags
        ];
        content = newPrivateItems.length
            ? await window.nostr.nip44.encrypt(state.publicKey, JSON.stringify(newPrivateItems))
            : '';
    }

    const ev = {
        kind: USER_EMOJI_LIST_KIND,
        created_at: Math.floor(Date.now() / 1000),
        tags: [...foreignTags, ...publicEmojiTags],
        content
    };
    const signed = await window.nostr.signEvent(ev);
    const targets = [...new Set([...(state.dmRelayUrls?.length ? state.dmRelayUrls : []), ...RELAY_URLS])];
    const publishAttempts = targets.map(async (url) => {
        await state.pool.publish([url], signed, { onauth: nostrAuthHandler });
        return url;
    });
    await Promise.any(publishAttempts);
    state.ownKind10030Event = signed;
    if (canEditPrivate) {
        state.ownKind10030PrivateItems = newPrivateItems;
    }
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
