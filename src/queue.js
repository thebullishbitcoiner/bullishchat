import { state } from './state.js';

// These functions are imported lazily from ui.js to avoid circular dependency at load time.
// ui.js imports sendReactionToMessage from messages.js; messages.js imports from queue.js.
// queue.js imports from ui.js — but only at call time (inside functions), not at module load time.

export function queueConversationsListUpdate() {
    if (state.conversationsListUpdateQueued) return;
    state.conversationsListUpdateQueued = true;
    requestAnimationFrame(() => {
        state.conversationsListUpdateQueued = false;
        // Lazy import to avoid circular dependency at module load time
        import('./ui.js').then(({ updateConversationsList }) => {
            updateConversationsList();
        });
    });
}

export function queueChatHeaderUpdate(pubkey) {
    if (state.currentChat !== pubkey || state.chatHeaderUpdateQueued) return;
    state.chatHeaderUpdateQueued = true;
    requestAnimationFrame(() => {
        state.chatHeaderUpdateQueued = false;
        if (state.currentChat === pubkey) {
            import('./ui.js').then(({ updateChatHeader }) => {
                updateChatHeader(pubkey);
            });
        }
    });
}

export function queueActiveChatRender(pubkey, opts = {}) {
    if (state.currentChat !== pubkey) return;
    state.activeChatRenderPubkey = pubkey;
    state.activeChatRenderNeedsHeader = state.activeChatRenderNeedsHeader || Boolean(opts.header);
    if (state.activeChatRenderTimer) return;
    state.activeChatRenderTimer = setTimeout(() => {
        const target = state.activeChatRenderPubkey;
        const shouldHeader = state.activeChatRenderNeedsHeader;
        state.activeChatRenderTimer = null;
        state.activeChatRenderPubkey = null;
        state.activeChatRenderNeedsHeader = false;
        if (!target || state.currentChat !== target) return;
        import('./ui.js').then(({ displayMessages, updateChatHeader }) => {
            displayMessages(target);
            if (shouldHeader) {
                updateChatHeader(target);
            }
        });
    }, 90);
}
