import * as nip19 from 'nostr-tools/nip19';

import { state } from './state.js';
import {
    normalizePubkey,
    MAX_CUSTOM_REACTION_EMOJIS,
    NOSTR_ARCHIVES_SEARCH_SUGGEST_URL
} from './constants.js';
import { getDisplayName, fetchUserProfile } from './profile.js';
import { resolveInboxRelays } from './relay.js';
import {
    sendReactionToMessage,
    payLightningInvoice,
    revokeActiveMessageBlobs,
    parseBolt11InvoiceFromText,
    appendRichMessageContent,
    loadKind15ImagePreview,
    formatConversationPreview,
    lastConversationSortTime
} from './messages.js';
import { fetchConversationRepair } from './sync.js';

export function setInboxLoading(loading) {
    state.isInboxLoading = Boolean(loading);
    const el = document.getElementById('inboxLoading');
    if (el) {
        el.hidden = !state.isInboxLoading;
    }
}

export function splitGraphemes(str) {
    if (!str) return [];
    if (typeof Intl !== 'undefined' && typeof Intl.Segmenter === 'function') {
        const seg = new Intl.Segmenter(undefined, { granularity: 'grapheme' });
        return [...seg.segment(str)].map((s) => s.segment);
    }
    return Array.from(str);
}

export function emojiShortcodeFromToken(token) {
    if (typeof token !== 'string') return '';
    const m = token.trim().match(/^:([a-zA-Z0-9_+-]+):$/);
    return m ? m[1] : '';
}

export function normalizeCustomEmojiLines(raw) {
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
    return out.slice(0, MAX_CUSTOM_REACTION_EMOJIS);
}

export function getTagValue(tags, key) {
    if (!Array.isArray(tags)) return '';
    const row = tags.find((t) => t[0] === key && typeof t[1] === 'string' && t[1].length);
    return row ? row[1] : '';
}

export function avatarInitialFromLabel(label, pubkey = '') {
    const base = (label || '').trim();
    if (base) {
        return base.slice(0, 1).toUpperCase();
    }
    return (pubkey || '?').slice(0, 1).toUpperCase();
}

export function createAvatarNode(pubkey, className = 'avatar') {
    const profile = state.userProfiles[pubkey];
    const picture = typeof profile?.picture === 'string' ? profile.picture.trim() : '';
    const canUsePicture = picture.length > 0 && !state.brokenAvatarUrls.has(picture);
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
            state.brokenAvatarUrls.add(picture);
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

export function updateAvatarHost(host, pubkey) {
    const profile = state.userProfiles[pubkey];
    const picture = typeof profile?.picture === 'string' ? profile.picture.trim() : '';
    const canUsePicture = picture.length > 0 && !state.brokenAvatarUrls.has(picture);
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
            state.brokenAvatarUrls.add(picture);
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

let activeConversationMenu = null;

function closeConversationMenu() {
    if (activeConversationMenu) {
        activeConversationMenu.menu.remove();
        document.removeEventListener('click', activeConversationMenu.onOutsideClick, true);
        activeConversationMenu = null;
    }
}

function openConversationMenu(item, pubkey, protocol) {
    const alreadyOpenOnThisItem = activeConversationMenu?.item === item;
    closeConversationMenu();
    if (alreadyOpenOnThisItem) return;

    const menu = document.createElement('div');
    menu.className = 'conversation-item-menu';
    menu.setAttribute('role', 'menu');

    const deleteBtn = document.createElement('button');
    deleteBtn.type = 'button';
    deleteBtn.className = 'conversation-item-menu-item';
    deleteBtn.setAttribute('role', 'menuitem');
    deleteBtn.textContent = 'Delete conversation';
    deleteBtn.addEventListener('click', async (e) => {
        e.stopPropagation();
        closeConversationMenu();
        if (!confirm('Delete this conversation on this device? If they message you again, a new conversation will appear.')) {
            return;
        }
        const { deleteConversationLocal } = await import('./messages.js');
        await deleteConversationLocal(pubkey, protocol);
    });

    const muteBtn = document.createElement('button');
    muteBtn.type = 'button';
    muteBtn.className = 'conversation-item-menu-item conversation-item-menu-item--danger';
    muteBtn.setAttribute('role', 'menuitem');
    muteBtn.textContent = 'Mute user';
    muteBtn.addEventListener('click', async (e) => {
        e.stopPropagation();
        closeConversationMenu();
        if (!confirm('Mute this user? Their messages will stop appearing here (both tabs) until you unmute them in Settings.')) {
            return;
        }
        const { muteConversation } = await import('./mute.js');
        await muteConversation(pubkey);
    });

    menu.appendChild(deleteBtn);
    menu.appendChild(muteBtn);
    item.appendChild(menu);

    const onOutsideClick = (e) => {
        if (!menu.contains(e.target)) {
            closeConversationMenu();
        }
    };
    activeConversationMenu = { item, menu, onOutsideClick };
    setTimeout(() => document.addEventListener('click', onOutsideClick, true), 0);
}

export function createConversationItem(pubkey, protocol = 'nip17') {
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

    const menuBtn = document.createElement('button');
    menuBtn.type = 'button';
    menuBtn.className = 'conversation-item-menu-btn';
    menuBtn.setAttribute('aria-label', 'Conversation options');
    menuBtn.setAttribute('aria-haspopup', 'true');
    menuBtn.textContent = '⋮';
    menuBtn.addEventListener('click', (e) => {
        e.stopPropagation();
        openConversationMenu(item, pubkey, protocol);
    });
    main.appendChild(menuBtn);

    item.appendChild(main);

    item.addEventListener('contextmenu', (e) => {
        e.preventDefault();
        openConversationMenu(item, pubkey, protocol);
    });

    // Swipe-left (mobile) opens the same menu as right-click/⋮. Only claims the gesture
    // once it's clearly more horizontal than vertical, so list scrolling still works.
    let swipeStartX = null;
    let swipeStartY = null;
    let swipeActive = false;
    let swipeTriggered = false;

    item.addEventListener('touchstart', (e) => {
        if (!isMobileLayout() || e.target.closest('.conversation-item-menu-btn')) {
            swipeStartX = null;
            return;
        }
        const t = e.touches[0];
        swipeStartX = t.clientX;
        swipeStartY = t.clientY;
        swipeActive = false;
        swipeTriggered = false;
    }, { passive: true });

    item.addEventListener('touchmove', (e) => {
        if (swipeStartX === null) return;
        const t = e.touches[0];
        const dx = t.clientX - swipeStartX;
        const dy = t.clientY - swipeStartY;
        if (!swipeActive) {
            if (Math.abs(dx) < 10 && Math.abs(dy) < 10) return;
            if (Math.abs(dx) <= Math.abs(dy)) {
                swipeStartX = null; // vertical scroll — let the browser handle it
                return;
            }
            swipeActive = true;
        }
        e.preventDefault();
        if (!swipeTriggered && dx < -60) {
            swipeTriggered = true;
            openConversationMenu(item, pubkey, protocol);
        }
    }, { passive: false });

    const endSwipe = (e) => {
        if (swipeTriggered) {
            e.preventDefault();
        }
        swipeStartX = null;
        swipeActive = false;
        swipeTriggered = false;
    };
    item.addEventListener('touchend', endSwipe, { passive: false });
    item.addEventListener('touchcancel', endSwipe, { passive: false });

    return { item, avatarHost, nameEl, dateEl, previewEl };
}

export function setNip04Unread(hasUnread) {
    state.nip04HasUnread = hasUnread;
    const dot = document.getElementById('nip04UnreadDot');
    if (dot) dot.hidden = !hasUnread;
}

export function switchConversationTab(tab) {
    state.activeConversationTab = tab;
    document.getElementById('tabNip17')?.classList.toggle('conv-tab--active', tab === 'nip17');
    document.getElementById('tabNip04')?.classList.toggle('conv-tab--active', tab === 'nip04');
    if (tab === 'nip04') setNip04Unread(false);
    updateConversationsList();
}

export function updateConversationsList() {
    const list = document.getElementById('conversationsList');
    // Switching tabs hides the other tab's rows as a side effect below, independent of whether the
    // underlying conversation data changed — so the fingerprint short-circuit must not apply on the
    // render right after a tab switch, or the rows it just hid may never get shown again.
    const tabChanged = state.activeConversationTab !== state.lastRenderedConversationsTab;
    state.lastRenderedConversationsTab = state.activeConversationTab;

    if (state.activeConversationTab === 'nip04') {
        // Hide NIP-17 rows
        for (const [, row] of state.conversationItemEls.entries()) row.item.hidden = true;

        const nip04Pubkeys = Object.keys(state.nip04Conversations).filter((pk) => !state.mutedPubkeys.has(pk)).sort(
            (a, b) => lastConversationSortTime(state.nip04Conversations[b]) - lastConversationSortTime(state.nip04Conversations[a])
        );

        const nip04Fingerprint = nip04Pubkeys.map((pk) => {
            const conv = state.nip04Conversations[pk];
            const lastMsg = conv.length > 0 ? conv[conv.length - 1] : null;
            const isActive = state.currentChat === pk && state.currentChatProtocol === 'nip04';
            const isUnread = state.unreadNip04.has(pk);
            return [pk, getDisplayName(pk), formatConversationPreview(lastMsg), lastMsg?.timestamp || 0, isActive ? 1 : 0, isUnread ? 1 : 0].join(':');
        }).join('|');
        if (!tabChanged && nip04Fingerprint === state.nip04ConversationsListFingerprint) {
            return;
        }
        state.nip04ConversationsListFingerprint = nip04Fingerprint;

        const seenNip04 = new Set();
        for (const pubkey of nip04Pubkeys) {
            seenNip04.add(pubkey);
            const conv = state.nip04Conversations[pubkey];
            const lastMsg = conv.length > 0 ? conv[conv.length - 1] : null;

            let row = state.nip04ConversationItemEls.get(pubkey);
            if (!row) {
                row = createConversationItem(pubkey, 'nip04');
                row.item.onclick = () => openNip04Chat(pubkey);
                state.nip04ConversationItemEls.set(pubkey, row);
            }

            const isActive = state.currentChat === pubkey && state.currentChatProtocol === 'nip04';
            const isUnread = state.unreadNip04.has(pubkey);
            row.item.hidden = false;
            row.item.className = 'conversation-item' + (isActive ? ' active' : '') + (isUnread ? ' unread' : '');
            row.nameEl.textContent = getDisplayName(pubkey);
            row.dateEl.textContent = lastMsg ? formatConversationDate(lastMsg.timestamp) : '';
            row.previewEl.textContent = formatConversationPreview(lastMsg);
            updateAvatarHost(row.avatarHost, pubkey);
            list.appendChild(row.item);
        }
        for (const [pubkey, row] of state.nip04ConversationItemEls.entries()) {
            if (!seenNip04.has(pubkey)) { row.item.remove(); state.nip04ConversationItemEls.delete(pubkey); }
        }
        return;
    }

    // NIP-17 tab
    // Hide NIP-04 rows
    for (const [, row] of state.nip04ConversationItemEls.entries()) row.item.hidden = true;

    const orderedPubkeys = Object.keys(state.conversations).filter((pk) => !state.mutedPubkeys.has(pk)).sort(
        (a, b) => lastConversationSortTime(state.conversations[b]) - lastConversationSortTime(state.conversations[a])
    );

    const fingerprint = orderedPubkeys.map((pk) => {
        const conv = state.conversations[pk];
        const lastMsg = conv.length > 0 ? conv[conv.length - 1] : null;
        const isActive = state.currentChat === pk && state.currentChatProtocol !== 'nip04';
        const isUnread = state.unreadNip17.has(pk);
        return [pk, getDisplayName(pk), formatConversationPreview(lastMsg), lastMsg?.timestamp || 0, isActive ? 1 : 0, isUnread ? 1 : 0].join(':');
    }).join('|');
    if (!tabChanged && fingerprint === state.conversationsListFingerprint) {
        return;
    }
    state.conversationsListFingerprint = fingerprint;

    const seen = new Set();
    for (const pubkey of orderedPubkeys) {
        seen.add(pubkey);
        const conv = state.conversations[pubkey];
        const lastMsg = conv.length > 0 ? conv[conv.length - 1] : null;

        let row = state.conversationItemEls.get(pubkey);
        if (!row) {
            row = createConversationItem(pubkey);
            state.conversationItemEls.set(pubkey, row);
        }

        const isActive = state.currentChat === pubkey && state.currentChatProtocol !== 'nip04';
        const isUnread = state.unreadNip17.has(pubkey);
        row.item.hidden = false;
        row.item.className = 'conversation-item' + (isActive ? ' active' : '') + (isUnread ? ' unread' : '');
        row.nameEl.textContent = getDisplayName(pubkey);
        row.dateEl.textContent = lastMsg ? formatConversationDate(lastMsg.timestamp) : '';
        row.previewEl.textContent = formatConversationPreview(lastMsg);
        updateAvatarHost(row.avatarHost, pubkey);
        list.appendChild(row.item);
    }
    for (const [pubkey, row] of state.conversationItemEls.entries()) {
        if (!seen.has(pubkey)) { row.item.remove(); state.conversationItemEls.delete(pubkey); }
    }
}

export function isMobileLayout() {
    return window.matchMedia('(max-width: 768px)').matches;
}

export function setMobileChatPanel(open) {
    document.querySelector('.container')?.classList.toggle('mobile-chat-visible', open);
}

export function openChat(pubkey) {
    import('./messages.js').then(({ clearPendingImage }) => clearPendingImage());
    state.currentChat = normalizePubkey(pubkey);
    state.currentChatProtocol = 'nip17';
    state.unreadNip17.delete(state.currentChat);
    document.getElementById('emptyState').style.display = 'none';
    document.getElementById('chatView').style.display = 'flex';

    // Show the chat column before measuring scroll (mobile hides it until this class is set).
    if (isMobileLayout()) {
        setMobileChatPanel(true);
    }

    updateChatHeader(pubkey);
    displayMessages(pubkey);
    updateConversationsList();
    void fetchConversationRepair(state.currentChat, { deep: true });
    void updateRightPanel(state.currentChat);
}

export function openNip04Chat(pubkey) {
    import('./messages.js').then(({ clearPendingImage }) => clearPendingImage());
    state.currentChat = normalizePubkey(pubkey);
    state.currentChatProtocol = 'nip04';
    state.unreadNip04.delete(state.currentChat);
    document.getElementById('emptyState').style.display = 'none';
    document.getElementById('chatView').style.display = 'flex';

    if (isMobileLayout()) {
        setMobileChatPanel(true);
    }

    updateChatHeader(pubkey);
    displayNip04Messages(pubkey);
    updateConversationsList();
    void updateRightPanel(state.currentChat);
}

export function backToConversations() {
    setMobileChatPanel(false);
    void updateRightPanel(null);
}

// Update chat header with display name
export function updateChatHeader(pubkey) {
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
export function formatTimestamp(timestamp) {
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
export function formatDateSeparator(timestamp) {
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
export function formatConversationDate(timestamp) {
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

/** Positions a fixed-position popover (message menu / reaction picker) from an anchor button's
 *  real screen coordinates, in #messagePopoverLayer — independent of any ancestor's width/overflow
 *  clipping, which is what made the old CSS-only (absolute, anchored-to-bubble) positioning break
 *  whenever the sidebar/right-panel left the chat column narrower than expected. */
function positionPopoverNearButton(el, anchorBtn, alignRight) {
    const margin = 6;
    const viewportMargin = 8;
    const btnRect = anchorBtn.getBoundingClientRect();
    const elRect = el.getBoundingClientRect();

    let left = alignRight ? btnRect.right - elRect.width : btnRect.left;
    let top = btnRect.bottom + margin;

    const vw = window.innerWidth;
    const vh = window.innerHeight;

    if (top + elRect.height > vh - viewportMargin) {
        top = btnRect.top - margin - elRect.height;
    }
    if (top < viewportMargin) {
        top = viewportMargin;
    }
    if (left + elRect.width > vw - viewportMargin) {
        left = vw - viewportMargin - elRect.width;
    }
    if (left < viewportMargin) {
        left = viewportMargin;
    }

    el.style.top = `${top}px`;
    el.style.left = `${left}px`;
}

let sharedReactionPickerPromise = null;

/** Lazily builds a single emoji-mart picker instance shared by every message row, instead of one
 *  per message. Building one per message left a window (dynamic-import fetch + first paint) during
 *  which an unrelated incoming message could trigger displayMessages() to wipe the popover layer,
 *  destroying the picker mid-construction — a persistent shared instance is never torn down by a
 *  conversation re-render, so that race can't happen. It gets retargeted (which message it reacts
 *  to) and repositioned (which button it's anchored to) on every open instead of rebuilt. */
function getSharedReactionPicker() {
    if (sharedReactionPickerPromise) return sharedReactionPickerPromise;

    sharedReactionPickerPromise = (async () => {
        const [{ Picker }, { default: emojiMartData }] = await Promise.all([
            import('emoji-mart'),
            import('@emoji-mart/data')
        ]);

        const customTokens = (state.customReactionEmojiSet || []).filter((token) => {
            const shortcode = emojiShortcodeFromToken(token);
            return shortcode && state.customReactionEmojiUrlMap[shortcode];
        });
        const custom = customTokens.length
            ? [{
                id: 'custom',
                name: 'Custom',
                emojis: customTokens.map((token) => {
                    const shortcode = emojiShortcodeFromToken(token);
                    return {
                        id: shortcode,
                        name: shortcode,
                        keywords: [shortcode],
                        skins: [{ src: state.customReactionEmojiUrlMap[shortcode] }]
                    };
                })
            }]
            : [];

        let currentMsg = null;
        let currentOnPick = null;

        const root = document.createElement('div');
        root.className = 'message-reaction-picker';
        root.hidden = true;

        const picker = new Picker({
            data: emojiMartData,
            custom,
            theme: 'dark',
            previewPosition: 'none',
            skinTonePosition: 'search',
            onEmojiSelect: (emoji) => {
                if (!currentMsg) return;
                const token = emoji.native || `:${emoji.id}:`;
                void sendReactionToMessage(currentMsg, token);
                if (typeof currentOnPick === 'function') currentOnPick();
            }
        });
        root.appendChild(picker);
        document.getElementById('messagePopoverLayer')?.appendChild(root);

        return {
            root,
            setTarget(msg, onPick) {
                currentMsg = msg;
                currentOnPick = onPick;
            }
        };
    })();

    return sharedReactionPickerPromise;
}

function hideSharedReactionPicker() {
    if (!sharedReactionPickerPromise) return;
    sharedReactionPickerPromise.then((shared) => {
        shared.root.hidden = true;
    });
}

function waitForNonZeroSize(el, framesLeft = 30) {
    return new Promise((resolve) => {
        const check = () => {
            const rect = el.getBoundingClientRect();
            if ((rect.width > 10 && rect.height > 10) || framesLeft <= 0) {
                resolve();
                return;
            }
            framesLeft -= 1;
            requestAnimationFrame(check);
        };
        check();
    });
}

/** ⋮ menu — message-level actions (View JSON, more later). Shared by nip17 and nip04 rendering. */
function buildMessageMenu(msg, options = {}) {
    const actionsEl = document.createElement('div');
    actionsEl.className = 'message-actions';

    const menuBtn = document.createElement('button');
    menuBtn.type = 'button';
    menuBtn.className = 'message-react-btn';
    menuBtn.setAttribute('aria-label', 'Message options');
    menuBtn.textContent = '⋮';

    const menu = document.createElement('div');
    menu.className = 'message-menu';
    menu.hidden = true;

    const copyTextBtn = document.createElement('button');
    copyTextBtn.type = 'button';
    copyTextBtn.className = 'message-menu-item';
    copyTextBtn.textContent = 'Copy Text';
    copyTextBtn.addEventListener('click', async (e) => {
        e.stopPropagation();
        menu.hidden = true;
        try {
            await navigator.clipboard.writeText(typeof msg.content === 'string' ? msg.content : '');
        } catch {
            // Clipboard unavailable (permissions, insecure context) — nothing to recover here.
        }
    });
    menu.appendChild(copyTextBtn);

    const viewJsonBtn = document.createElement('button');
    viewJsonBtn.type = 'button';
    viewJsonBtn.className = 'message-menu-item';
    viewJsonBtn.textContent = 'View JSON';
    viewJsonBtn.addEventListener('click', (e) => {
        e.stopPropagation();
        menu.hidden = true;
        openViewJsonModal(msg);
    });
    menu.appendChild(viewJsonBtn);

    menuBtn.addEventListener('click', (e) => {
        e.stopPropagation();
        document.querySelectorAll('.message-menu').forEach((el) => {
            if (el !== menu) el.hidden = true;
        });
        if (typeof options.onOpen === 'function') {
            options.onOpen();
        }
        const willOpen = menu.hidden;
        menu.hidden = !willOpen;
        if (willOpen) {
            positionPopoverNearButton(menu, menuBtn, true);
        }
    });

    document.getElementById('messagePopoverLayer')?.appendChild(menu);
    actionsEl.appendChild(menuBtn);
    return { actionsEl, menu, menuBtn };
}

export function displayMessages(pubkey) {
    const messages = state.conversations[pubkey] || [];
    // Sync polls call queueActiveChatRender() unconditionally whether or not anything new actually
    // arrived. Without this guard, every one of those no-op polls would still fully rebuild the
    // thread (visible flash) and close any reaction picker the user had open at the time.
    const fingerprint = 'nip17::' + pubkey + '::' + messages.map(
        (m) => `${m.id}:${m.timestamp}:${m.reactions ? Object.keys(m.reactions).length : 0}`
    ).join('|');
    if (fingerprint === state.displayedMessagesFingerprint) {
        return;
    }
    state.displayedMessagesFingerprint = fingerprint;

    const container = document.getElementById('messagesContainer');
    revokeActiveMessageBlobs();
    container.innerHTML = '';
    // Per-message ⋮ menus are cheap to recreate, so drop the stale ones outright. The shared
    // reaction picker is NOT torn down here — it's a single persistent instance (see
    // getSharedReactionPicker) — just hidden, since the message it was targeting no longer exists.
    document.querySelectorAll('#messagePopoverLayer .message-menu').forEach((el) => el.remove());
    hideSharedReactionPicker();

    if (!state.conversations[pubkey]) return;

    let lastDate = null;

    state.conversations[pubkey].forEach((msg) => {
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
        div.className = 'message ' + (msg.from === state.publicKey ? 'sent' : 'received');

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
            // Reaction picker — opened via long-press (touch hold or mouse press-and-hold), not the
            // ⋮ button. Retargets the single shared emoji-mart instance instead of building its own.
            const { actionsEl, menuBtn } = buildMessageMenu(msg, {
                onOpen: hideSharedReactionPicker
            });

            const openPicker = () => {
                document.querySelectorAll('.message-menu').forEach((el) => {
                    el.hidden = true;
                });
                getSharedReactionPicker().then(async (shared) => {
                    shared.setTarget(msg, () => {
                        shared.root.hidden = true;
                    });
                    shared.root.hidden = false;
                    // Rough placement immediately (usually already correct — the shadow-DOM content
                    // was built while hidden, and un-hiding forces a synchronous layout). Then confirm
                    // it actually has real dimensions and refine, in case that first read raced ahead
                    // of paint on a slower device.
                    positionPopoverNearButton(shared.root, menuBtn, true);
                    await waitForNonZeroSize(shared.root);
                    if (!shared.root.hidden) {
                        positionPopoverNearButton(shared.root, menuBtn, true);
                    }
                });
            };

            let longPressTimer = null;
            // The mouseup/touchend that ends a long-press also fires a native "click" on this
            // element right after, which would otherwise bubble to the document-level outside-click
            // closer and immediately hide the picker we just opened. Swallow exactly that one click.
            let suppressNextClick = false;
            const clearLongPress = () => {
                if (longPressTimer) {
                    clearTimeout(longPressTimer);
                    longPressTimer = null;
                }
            };
            const startLongPress = () => {
                clearLongPress();
                longPressTimer = setTimeout(() => {
                    suppressNextClick = true;
                    openPicker();
                }, 420);
            };

            div.addEventListener('click', (e) => {
                if (suppressNextClick) {
                    suppressNextClick = false;
                    e.stopPropagation();
                }
            });

            div.addEventListener('touchstart', (e) => {
                if (e.target.closest('button, a')) {
                    return;
                }
                startLongPress();
            }, { passive: true });
            div.addEventListener('touchend', clearLongPress, { passive: true });
            div.addEventListener('touchcancel', clearLongPress, { passive: true });
            div.addEventListener('touchmove', clearLongPress, { passive: true });

            div.addEventListener('mousedown', (e) => {
                if (e.button !== 0 || e.target.closest('button, a')) {
                    return;
                }
                startLongPress();
            });
            div.addEventListener('mouseup', clearLongPress);
            div.addEventListener('mouseleave', clearLongPress);

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
                    const url = shortcode ? state.customReactionEmojiUrlMap[shortcode] : '';
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
                    if (Array.isArray(info?.reactors) && info.reactors.includes(state.publicKey)) {
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

export function displayNip04Messages(pubkey) {
    const nip04Messages = state.nip04Conversations[pubkey] || [];
    const fingerprint = 'nip04::' + pubkey + '::' + nip04Messages.map((m) => `${m.id}:${m.timestamp}`).join('|');
    if (fingerprint === state.displayedMessagesFingerprint) {
        return;
    }
    state.displayedMessagesFingerprint = fingerprint;

    const container = document.getElementById('messagesContainer');
    revokeActiveMessageBlobs();
    container.innerHTML = '';
    document.querySelectorAll('#messagePopoverLayer .message-menu').forEach((el) => el.remove());
    hideSharedReactionPicker();

    const banner = document.createElement('div');
    banner.className = 'nip04-banner';
    banner.textContent = '⚠ NIP-04 — legacy encryption, metadata visible to relays';
    container.appendChild(banner);

    if (!state.nip04Conversations[pubkey]) return;

    let lastDate = null;

    state.nip04Conversations[pubkey].forEach((msg) => {
        const msgDate = new Date(msg.timestamp * 1000);
        const currentDate = new Date(msgDate.getFullYear(), msgDate.getMonth(), msgDate.getDate());

        if (lastDate === null || currentDate.getTime() !== lastDate.getTime()) {
            const dateSeparator = document.createElement('div');
            dateSeparator.className = 'date-separator';
            dateSeparator.textContent = formatDateSeparator(msg.timestamp);
            container.appendChild(dateSeparator);
            lastDate = currentDate;
        }

        const div = document.createElement('div');
        div.className = 'message ' + (msg.from === state.publicKey ? 'sent' : 'received');

        const bodyEl = document.createElement('div');
        bodyEl.className = 'message-body';
        const parsedInvoice = parseBolt11InvoiceFromText(msg.content);
        if (parsedInvoice) {
            div.classList.add('message-invoice');
            if (parsedInvoice.cleanedText) appendRichMessageContent(bodyEl, parsedInvoice.cleanedText);
            const invoiceCard = document.createElement('div');
            invoiceCard.className = 'invoice-card';
            const amtEl = document.createElement('div');
            amtEl.className = 'invoice-amount';
            const msats = parsedInvoice.decoded?.satoshi != null ? parsedInvoice.decoded.satoshi * 1000 : null;
            amtEl.textContent = msats != null ? `${(msats / 1000).toLocaleString()} sats` : 'Lightning Invoice';
            invoiceCard.appendChild(amtEl);
            bodyEl.appendChild(invoiceCard);
        } else {
            appendRichMessageContent(bodyEl, msg.content);
        }

        const timeEl = document.createElement('div');
        timeEl.className = 'message-time';
        timeEl.textContent = new Date(msg.timestamp * 1000).toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });

        if (msg.id) {
            const { actionsEl } = buildMessageMenu(msg);
            div.appendChild(actionsEl);
        }

        div.appendChild(bodyEl);
        div.appendChild(timeEl);
        container.appendChild(div);
    });

    const scrollToBottom = () => { container.scrollTop = container.scrollHeight; };
    scrollToBottom();
    requestAnimationFrame(() => { scrollToBottom(); requestAnimationFrame(scrollToBottom); });
}

export function initImageLightbox() {
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

export function openImageLightbox(src) {
    if (!src) return;
    const lightbox = document.getElementById('imageLightbox');
    const img = document.getElementById('imageLightboxImg');
    if (!lightbox || !img) return;
    img.src = src;
    lightbox.hidden = false;
    syncBodyOverlayLock();
}

export function closeImageLightbox() {
    const lightbox = document.getElementById('imageLightbox');
    const img = document.getElementById('imageLightboxImg');
    if (!lightbox || !img) return;
    lightbox.hidden = true;
    img.removeAttribute('src');
    syncBodyOverlayLock();
}

export function insertAtCursor(textarea, text) {
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

/** Grapheme-safe emoji list for the in-app picker (Array.from preserves surrogate pairs). */
const EMOJI_PICKER_CHARS = Array.from(
    '😀😃😄😁😅😂🤣🥲😊😇🙂😉😌😍🥰😘😗😙😚😋😛😜🤪🤑🤗🤭🤔🤐🤨😐😑😏😒🙄😬🤥😪🤤😴🥱😮😯😲😳🥺😦😧😨😰😥😢😭😱😖😣😞😓😩😫🤯🤠🥳🥸😎🤓🧐😕😟🙁☹️😡🤬😈👿🤡💀☠️💩👻👽👾🤖💋💘💝💖💗💓💞💕💟❣️💔❤️🧡💛💚💙💜🤎🖤🤍💯💢💥💫💦💨👋🤚🖐️✋🖖👌🤌✌️🤞🤟🤘🤙👍👎✊👏🙌👐🤲🤝🙏✍️💪🦾🫶👀👂🦻👃🧠💬🗨️👁️💤🔥✨⭐🌟💫⚡🎉🎊✅❌❓❗📌📎🔗🧵🍻☕🫖🎯🏆🎮'
);

export function initEmojiPicker() {
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

export function openNewChatModal() {
    const modal = document.getElementById('newChatModal');
    const input = document.getElementById('newChatSearch');
    const sugg = document.getElementById('newChatSuggestions');
    const status = document.getElementById('newChatSearchStatus');
    const title = document.getElementById('newChatModalTitle');
    if (!modal || !input) {
        return;
    }
    closeFabMenu();
    state.profileSearchSerial += 1;
    state.profileSearchAbort?.abort();
    if (state.profileSearchDebounceTimer) {
        clearTimeout(state.profileSearchDebounceTimer);
    }
    modal.hidden = false;
    input.value = '';
    if (sugg) {
        sugg.innerHTML = '';
        sugg.hidden = true;
    }
    if (title) {
        title.textContent = state.activeConversationTab === 'nip04' ? 'New NIP-04 Chat' : 'New Chat';
    }
    if (status) {
        status.textContent = state.activeConversationTab === 'nip04'
            ? 'Type a name, paste a full npub, or enter a 64-character hex pubkey. Messages will use legacy NIP-04 encryption.'
            : 'Type a name, paste a full npub, or enter a 64-character hex pubkey.';
    }
    syncBodyOverlayLock();
    setTimeout(() => input.focus(), 50);
}

export function closeNewChatModal() {
    const modal = document.getElementById('newChatModal');
    if (modal) {
        modal.hidden = true;
    }
    syncBodyOverlayLock();
    state.profileSearchAbort?.abort();
    if (state.profileSearchDebounceTimer) {
        clearTimeout(state.profileSearchDebounceTimer);
    }
    state.profileSearchSerial += 1;
}

export function closeFabMenu() {
    const menu = document.getElementById('fabMenu');
    const btn = document.getElementById('fabPlusBtn');
    if (menu) {
        menu.hidden = true;
    }
    if (btn) {
        btn.setAttribute('aria-expanded', 'false');
    }
}

export function toggleFabMenu() {
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

export function isOverlayOpen() {
    const modal = document.getElementById('newChatModal');
    const settings = document.getElementById('settingsPage');
    const lightbox = document.getElementById('imageLightbox');
    const viewJson = document.getElementById('viewJsonModal');
    return Boolean(
        (modal && !modal.hidden) ||
        (settings && !settings.hidden) ||
        (lightbox && !lightbox.hidden) ||
        (viewJson && !viewJson.hidden)
    );
}

export function openViewJsonModal(msg) {
    const modal = document.getElementById('viewJsonModal');
    const body = document.getElementById('viewJsonBody');
    if (!modal || !body || !msg) return;
    const display = {
        id: msg.id,
        pubkey: msg.pubkey || msg.from,
        created_at: msg.timestamp,
        kind: msg.kind,
        tags: msg.tags || [],
        content: msg.content
    };
    if (msg.sig) {
        display.sig = msg.sig;
    }
    body.textContent = JSON.stringify(display, null, 2);
    modal.hidden = false;
    syncBodyOverlayLock();
}

export function closeViewJsonModal() {
    const modal = document.getElementById('viewJsonModal');
    if (modal) {
        modal.hidden = true;
    }
    syncBodyOverlayLock();
}

export function initMessageMenus() {
    document.addEventListener('click', (e) => {
        // composedPath (not e.target) because emoji-mart renders inside a shadow root — a click on
        // one of its internal category tabs gets retargeted to the shadow host at this listener,
        // but composedPath still lets us see it's inside .message-reaction-picker so we don't treat
        // it as an "outside" click and close the picker the user is actively using.
        const path = typeof e.composedPath === 'function' ? e.composedPath() : [e.target];
        const isClassMatch = (el, cls) => el instanceof Element && el.classList.contains(cls);
        const insideMenu = path.some((el) => isClassMatch(el, 'message-menu'));
        const insidePicker = path.some((el) => isClassMatch(el, 'message-reaction-picker'));

        if (!insideMenu) {
            document.querySelectorAll('.message-menu').forEach((el) => {
                el.hidden = true;
            });
        }
        if (!insidePicker) {
            document.querySelectorAll('.message-reaction-picker').forEach((el) => {
                el.hidden = true;
            });
        }
    });
}

export function initViewJsonModal() {
    const modal = document.getElementById('viewJsonModal');
    const closeBtn = document.getElementById('viewJsonModalClose');
    const copyBtn = document.getElementById('viewJsonCopyBtn');
    if (!modal) return;

    closeBtn?.addEventListener('click', closeViewJsonModal);
    modal.addEventListener('click', (e) => {
        if (e.target === modal) closeViewJsonModal();
    });
    copyBtn?.addEventListener('click', async () => {
        const body = document.getElementById('viewJsonBody');
        try {
            await navigator.clipboard.writeText(body?.textContent || '');
            copyBtn.textContent = '✓';
        } catch {
            copyBtn.textContent = '!';
        }
        setTimeout(() => {
            copyBtn.textContent = '⧉';
        }, 1200);
    });
}

export function syncBodyOverlayLock() {
    document.body.style.overflow = isOverlayOpen() ? 'hidden' : '';
}

export function buildSearchHit(pubkey, displayName = null, picture = null, followerCount = null, nip05 = null) {
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
        const npub = nip19.npubEncode(pk);
        npubDisplay = npub.length > 22 ? `${npub.slice(0, 11)}:${npub.slice(-11)}` : npub;
    } catch {
        /* keep short hex */
    }
    return { pubkey: pk, label, npubDisplay, picture, followerCount, nip05 };
}

export function formatFollowerCount(value) {
    if (!Number.isFinite(value) || value < 0) {
        return '';
    }
    const rounded = Math.round(value);
    const compact = new Intl.NumberFormat(undefined, { notation: 'compact', maximumFractionDigits: 1 }).format(rounded);
    return `${compact} follower${rounded === 1 ? '' : 's'}`;
}

export async function throttleProfileSearch() {
    // Keep comfortably below API limits while preserving quick typeahead UX.
    const gap = 550 - (Date.now() - state.lastProfileSearchRequestMs);
    if (gap > 0) {
        await new Promise((r) => setTimeout(r, gap));
    }
    state.lastProfileSearchRequestMs = Date.now();
}

/**
 * @param {string} query
 * @param {AbortSignal} signal
 * @returns {Promise<Array<{ pubkey: string, label: string, npubDisplay: string, picture: string | null, followerCount: number | null, nip05: string | null }>>}
 */
export async function fetchNostrUserSuggestions(query, signal) {
    const q = query.trim();
    if (!q) {
        return [];
    }

    if (/^[a-fA-F0-9]{64}$/.test(q)) {
        const pk = normalizePubkey(q);
        if (state.publicKey && pk === state.publicKey) {
            return [];
        }
        return [buildSearchHit(pk)];
    }

    if (q.startsWith('npub')) {
        try {
            const decoded = nip19.decode(q);
            if (decoded.type === 'npub') {
                const pk = normalizePubkey(decoded.data);
                if (state.publicKey && pk === state.publicKey) {
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

    await throttleProfileSearch();
    if (signal.aborted) {
        return [];
    }

    const url = `${NOSTR_ARCHIVES_SEARCH_SUGGEST_URL}?${new URLSearchParams({ q, limit: '10' })}`;
    const res = await fetch(url, { signal, headers: { Accept: 'application/json' } });
    if (!res.ok) {
        throw new Error(`Search failed (${res.status})`);
    }
    const json = await res.json();
    const seen = new Set();
    const hits = [];

    const suggestions = Array.isArray(json?.suggestions) ? json.suggestions : [];
    for (const suggestion of suggestions) {
        if (!suggestion?.pubkey) {
            continue;
        }
        const pk = normalizePubkey(suggestion.pubkey);
        if (state.publicKey && pk === state.publicKey) {
            continue;
        }
        if (seen.has(pk)) {
            continue;
        }
        seen.add(pk);

        let label = pk.slice(0, 8) + '…' + pk.slice(-6);
        let picture = null;
        let followerCount = null;
        let nip05 = null;
        label = suggestion.display_name || suggestion.displayName || suggestion.name || label;
        picture = typeof suggestion.picture === 'string' && suggestion.picture.length > 0 ? suggestion.picture : null;
        if (Number.isFinite(suggestion.follower_count)) {
            followerCount = Number(suggestion.follower_count);
        }
        if (typeof suggestion.nip05 === 'string' && suggestion.nip05.trim()) {
            nip05 = suggestion.nip05.trim();
        }
        hits.push(buildSearchHit(pk, label, picture, followerCount, nip05));
        if (hits.length >= 16) {
            break;
        }
    }
    return hits;
}

export function scheduleNewChatSearch(raw) {
    state.profileSearchAbort?.abort();
    const serial = ++state.profileSearchSerial;
    const statusEl = document.getElementById('newChatSearchStatus');
    const suggEl = document.getElementById('newChatSuggestions');

    if (state.profileSearchDebounceTimer) {
        clearTimeout(state.profileSearchDebounceTimer);
    }

    state.profileSearchDebounceTimer = setTimeout(async () => {
        state.profileSearchAbort = new AbortController();
        const { signal } = state.profileSearchAbort;
        const q = raw.trim();

        try {
            if (q.length === 0) {
                if (statusEl) {
                    statusEl.textContent =
                        'Type a name, paste a full npub, or enter a 64-character hex pubkey.';
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
            if (serial !== state.profileSearchSerial) {
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
            if (serial !== state.profileSearchSerial) {
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

export function renderNewChatSuggestions(hits) {
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
        if (typeof hit.nip05 === 'string' && hit.nip05.trim()) {
            const nip05El = document.createElement('span');
            nip05El.className = 'new-chat-suggestion-nip05';
            nip05El.textContent = ` ${hit.nip05.trim()}`;
            nameEl.appendChild(nip05El);
        }
        const npubEl = document.createElement('div');
        npubEl.className = 'new-chat-suggestion-npub';
        npubEl.textContent = hit.npubDisplay;
        text.appendChild(nameEl);
        text.appendChild(npubEl);
        if (Number.isFinite(hit.followerCount) && hit.followerCount >= 0) {
            const followerEl = document.createElement('div');
            followerEl.className = 'new-chat-suggestion-followers';
            followerEl.textContent = formatFollowerCount(hit.followerCount);
            text.appendChild(followerEl);
        }

        row.appendChild(avEl);
        row.appendChild(text);

        row.addEventListener('click', () => {
            void beginChatWithPubkey(hit.pubkey, hit);
        });
        root.appendChild(row);
    }
    root.hidden = false;
}

export function makeAvatarPlaceholder(hit) {
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

export async function beginChatWithPubkey(hex, hit = null) {
    const pk = normalizePubkey(hex);
    if (state.publicKey && pk === state.publicKey) {
        alert('You cannot start a chat with yourself.');
        return;
    }

    try {
        const useNip04 = state.activeConversationTab === 'nip04';
        if (useNip04) {
            if (!state.nip04Conversations[pk]) {
                state.nip04Conversations[pk] = [];
            }
        } else if (!state.conversations[pk]) {
            state.conversations[pk] = [];
        }
        if (hit) {
            state.userProfiles[pk] = {
                name: hit.label,
                display_name: hit.label,
                picture: hit.picture,
                about: state.userProfiles[pk]?.about ?? null,
            };
        }
        await fetchUserProfile(pk);
        closeNewChatModal();
        closeFabMenu();
        if (useNip04) {
            openNip04Chat(pk);
        } else {
            openChat(pk);
        }
    } catch (error) {
        alert('Could not open chat: ' + (error?.message || String(error)));
    }
}

export function initNewChatUi() {
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
        const settingsEl = document.getElementById('settingsPage');
        if (settingsEl && !settingsEl.hidden) {
            // import lazily to avoid circular; Esc backs out one level (section → menu → closed)
            import('./settings.js').then(({ settingsPageBack }) => {
                settingsPageBack();
            });
            e.preventDefault();
            return;
        }
        closeFabMenu();
    });
}

/**
 * Shows the resolved inbox relays (kind 10050/NIP-65) once discovery has run. Bootstrap/default
 * relays are connection plumbing, not something the user configured, so they're never shown.
 * Before discovery finishes, call with no args to leave the panel empty; once discovery has
 * actually run, pass `attempted: true` so a 0-result outcome renders an explanatory empty state
 * instead of silently leaving no card at all (that read as a bug rather than "nothing found").
 */
export function updateRelayStatusCard(inboxResults = [], { attempted = false } = {}) {
    const body = document.getElementById('rightPanelBody');
    const panel = document.getElementById('rightPanel');
    if (!body || !panel) return;

    panel.removeAttribute('hidden');

    const existing = document.getElementById('relayStatusCard');
    if (existing) existing.remove();

    if (!inboxResults.length && !attempted) return;

    const card = document.createElement('div');
    card.className = 'right-panel-card';
    card.id = 'relayStatusCard';

    const titleEl = document.createElement('div');
    titleEl.className = 'right-panel-card-title';
    card.appendChild(titleEl);

    if (!inboxResults.length) {
        titleEl.textContent = 'Relays';
        const empty = document.createElement('p');
        empty.className = 'right-panel-empty';
        empty.textContent = 'No inbox relays published. Go to Settings → DM Inbox Relays to configure them.';
        card.appendChild(empty);
    } else {
        const connected = inboxResults.filter((r) => r.success).length;
        titleEl.textContent = `Relays · ${connected}/${inboxResults.length}`;

        for (const { url, success } of inboxResults) {
            const row = document.createElement('div');
            row.className = `right-panel-relay${success ? '' : ' right-panel-relay--error'}`;
            row.textContent = url.replace(/^wss?:\/\//, '').replace(/\/$/, '');
            card.appendChild(row);
        }
    }

    body.insertBefore(card, body.firstChild);
}

export async function updateRightPanel(pubkey) {
    const body = document.getElementById('rightPanelBody');
    if (!body) return;

    const existing = document.getElementById('conversationRelayCard');
    if (existing) existing.remove();

    if (!pubkey) return;

    const card = document.createElement('div');
    card.className = 'right-panel-card';
    card.id = 'conversationRelayCard';

    const titleEl = document.createElement('div');
    titleEl.className = 'right-panel-card-title';
    titleEl.textContent = `${getDisplayName(pubkey)}'s Inbox Relays`;
    card.appendChild(titleEl);

    const loading = document.createElement('p');
    loading.className = 'right-panel-empty';
    loading.textContent = 'Loading…';
    card.appendChild(loading);

    body.appendChild(card);

    const relays = await resolveInboxRelays(pubkey);
    if (!card.contains(loading)) return;
    card.removeChild(loading);

    if (!relays.length) {
        const empty = document.createElement('p');
        empty.className = 'right-panel-empty';
        empty.textContent = 'No inbox relays published.';
        card.appendChild(empty);
        return;
    }

    for (const url of relays) {
        const row = document.createElement('div');
        row.className = 'right-panel-relay';
        row.textContent = url.replace(/^wss?:\/\//, '').replace(/\/$/, '');
        card.appendChild(row);
    }
}
