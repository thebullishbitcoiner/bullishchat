import { state } from './state.js';
import { RELAY_URLS, MUTE_LIST_KIND, normalizePubkey } from './constants.js';
import { idbPut, idbDeleteConversationMessages } from './db.js';
import { nostrAuthHandler } from './relay.js';

/** NIP-04 ciphertext carries its IV as a `?iv=` suffix; NIP-44 payloads never contain it. */
function isNip04Ciphertext(content) {
    return typeof content === 'string' && content.includes('?iv=');
}

function pubkeysFromTagList(tags) {
    return (Array.isArray(tags) ? tags : [])
        .filter((t) => Array.isArray(t) && t[0] === 'p' && typeof t[1] === 'string' && t[1].length)
        .map((t) => normalizePubkey(t[1]));
}

function rebuildMutedSet() {
    state.mutedPubkeys = new Set([
        ...pubkeysFromTagList(state.muteListPublicTags),
        ...pubkeysFromTagList(state.muteListPrivateItems)
    ]);
    void idbPut('meta', { key: 'mutedPubkeys', value: [...state.mutedPubkeys] }).catch(() => {});
}

/**
 * Fetch this user's newest kind 10000 mute list. Both halves are kept verbatim so a
 * publish never wipes entries another client wrote — plaintext tags, non-p items
 * (words/hashtags/threads), or a NIP-04-encrypted content blob.
 */
export async function loadMuteListFromNostr() {
    if (!state.pool || !state.publicKey) return;
    try {
        const relays = [...new Set([...(state.dmRelayUrls?.length ? state.dmRelayUrls : []), ...RELAY_URLS])];
        const events = await state.pool.querySync(
            relays,
            { kinds: [MUTE_LIST_KIND], authors: [state.publicKey], limit: 5 },
            { maxWait: 9000, onauth: nostrAuthHandler }
        );
        const newest = (events || []).sort((a, b) => (b.created_at || 0) - (a.created_at || 0))[0];
        if (!newest) return; // no list on relays — keep whatever IDB restored

        state.muteListPublicTags = Array.isArray(newest.tags) ? newest.tags : [];
        state.muteListPrivateItems = [];
        state.muteListRawContent = newest.content || '';
        state.muteListContentUnreadable = false;

        if (newest.content) {
            try {
                const decrypted = isNip04Ciphertext(newest.content) && window.nostr?.nip04?.decrypt
                    ? await window.nostr.nip04.decrypt(state.publicKey, newest.content)
                    : await window.nostr.nip44.decrypt(state.publicKey, newest.content);
                const parsed = JSON.parse(decrypted);
                if (Array.isArray(parsed)) {
                    state.muteListPrivateItems = parsed;
                } else {
                    state.muteListContentUnreadable = true;
                }
            } catch (e) {
                state.muteListContentUnreadable = true;
                console.warn('Mute list content could not be decrypted — private entries will be preserved verbatim:', e);
            }
        }

        rebuildMutedSet();

        // A mute made on another device/client may not have purged this device's local cache yet.
        for (const pk of state.mutedPubkeys) {
            if (state.conversations[pk] || state.nip04Conversations[pk]) {
                await purgeConversationEverywhere(pk);
            }
        }
    } catch (e) {
        console.warn('loadMuteListFromNostr failed:', e);
    }
}

async function publishMuteList() {
    if (!state.pool || !state.publicKey) return;
    try {
        // If the existing private blob was unreadable, republish it byte-for-byte rather
        // than replacing it with only what we know about.
        const content = state.muteListContentUnreadable
            ? state.muteListRawContent
            : (state.muteListPrivateItems.length
                ? await window.nostr.nip44.encrypt(state.publicKey, JSON.stringify(state.muteListPrivateItems))
                : '');
        const ev = {
            kind: MUTE_LIST_KIND,
            created_at: Math.floor(Date.now() / 1000),
            tags: state.muteListPublicTags,
            content
        };
        const signed = await window.nostr.signEvent(ev);
        if (!state.muteListContentUnreadable) {
            state.muteListRawContent = content;
        }
        const targets = [...new Set([...(state.dmRelayUrls?.length ? state.dmRelayUrls : []), ...RELAY_URLS])];
        const publishAttempts = targets.map((url) => state.pool.publish([url], signed, { onauth: nostrAuthHandler }));
        await Promise.any(publishAttempts);
    } catch (e) {
        console.warn('publishMuteList failed (mute is still applied locally):', e);
    }
}

/** Removes a peer's local conversation from both protocols' state + IndexedDB + UI. */
async function purgeConversationEverywhere(pubkey) {
    delete state.conversations[pubkey];
    delete state.nip04Conversations[pubkey];
    state.unreadNip17.delete(pubkey);
    state.unreadNip04.delete(pubkey);
    if (state.currentChat === pubkey) {
        state.currentChat = null;
        state.currentChatProtocol = null;
        const emptyState = document.getElementById('emptyState');
        if (emptyState) emptyState.style.display = 'flex';
        const chatView = document.getElementById('chatView');
        if (chatView) chatView.style.display = 'none';
        const { setMobileChatPanel, isMobileLayout } = await import('./ui.js');
        if (isMobileLayout()) setMobileChatPanel(false);
    }
    const nip17Row = state.conversationItemEls.get(pubkey);
    if (nip17Row) { nip17Row.item.remove(); state.conversationItemEls.delete(pubkey); }
    const nip04Row = state.nip04ConversationItemEls.get(pubkey);
    if (nip04Row) { nip04Row.item.remove(); state.nip04ConversationItemEls.delete(pubkey); }

    await Promise.all([
        idbDeleteConversationMessages('messages', pubkey),
        idbDeleteConversationMessages('nip04Messages', pubkey)
    ]);

    const { updateConversationsList } = await import('./ui.js');
    updateConversationsList();
}

export function isMuted(pubkey) {
    return state.mutedPubkeys.has(pubkey);
}

/** Mutes a pubkey: hides + purges their conversations now, and blocks their messages going forward. */
export async function muteConversation(pubkey) {
    const pk = normalizePubkey(pubkey);
    state.mutedPubkeys.add(pk);
    void idbPut('meta', { key: 'mutedPubkeys', value: [...state.mutedPubkeys] }).catch(() => {});
    await purgeConversationEverywhere(pk);

    if (state.muteListContentUnreadable) {
        // Can't merge into a blob we can't read — the mute still works on this device.
        console.warn('Mute applied locally only: existing kind 10000 private content is not decryptable by this extension.');
        return;
    }
    if (!pubkeysFromTagList(state.muteListPrivateItems).includes(pk) &&
        !pubkeysFromTagList(state.muteListPublicTags).includes(pk)) {
        state.muteListPrivateItems.push(['p', pk]);
    }
    void publishMuteList();
}

/** Unmutes a pubkey, removing it from both the plaintext tags and the private items. */
export async function unmuteConversation(pubkey) {
    const pk = normalizePubkey(pubkey);
    state.mutedPubkeys.delete(pk);
    void idbPut('meta', { key: 'mutedPubkeys', value: [...state.mutedPubkeys] }).catch(() => {});

    const dropPk = (t) => !(Array.isArray(t) && t[0] === 'p' && normalizePubkey(t[1] || '') === pk);
    state.muteListPublicTags = state.muteListPublicTags.filter(dropPk);
    if (!state.muteListContentUnreadable) {
        state.muteListPrivateItems = state.muteListPrivateItems.filter(dropPk);
    }
    void publishMuteList();
}
