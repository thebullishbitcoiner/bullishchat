import pkg from '../package.json';
import { SimplePool } from 'nostr-tools';

import { state } from './state.js';
import { RELAY_URLS, normalizePubkey } from './constants.js';
import { initDB, loadStateFromDB, loadNip04StateFromDB, idbPut } from './db.js';
import {
    connectRelaySet,
    resolveInboxRelays,
    fetchKind10063Servers,
} from './relay.js';
import { prefetchMissingConversationProfiles } from './profile.js';
import {
    subscribeToMessages,
    sendMessage,
    sendImageMessage,
    clearPendingImage,
    subscribeToNip04Messages
} from './messages.js';
import {
    resetSessionSyncState,
    startIncrementalInboxSync,
    stopIncrementalInboxSync,
    startIncrementalNip04Sync,
    stopIncrementalNip04Sync,
    fetchHistoricalGiftWraps,
    loadHistoricalNip04Messages,
    updateSettingsSyncUiState,
    scheduleMobileCatchup
} from './sync.js';
import {
    updateConversationsList,
    setInboxLoading,
    initEmojiPicker,
    initNewChatUi,
    initImageLightbox,
    isMobileLayout,
    setMobileChatPanel,
    backToConversations,
    displayMessages,
    updateChatHeader,
    updateRelayStatusCard,
    switchConversationTab
} from './ui.js';
import { initSettingsUi, loadOwnCustomReactionSetFromNostr } from './settings.js';

// Check if NIP-07 extension is available
function hasNostrExtension() {
    return typeof window.nostr !== 'undefined';
}

async function connectWithExtension() {
    if (!hasNostrExtension()) {
        alert('No Nostr extension detected!\n\nPlease install a NIP-07 compatible extension:\n\n• Alby (recommended) — https://getalby.com/\n• nos2x — https://github.com/fiatjaf/nos2x\n• Flamingo — https://getflamingo.org/\n• horse — https://github.com/fiatjaf/horse\n\nAfter installing, refresh this page and try again.');
        return;
    }

    const loginBtn = document.querySelector('.btn-landing');
    if (loginBtn) {
        loginBtn.disabled = true;
        loginBtn.textContent = 'Connecting…';
    }

    try {
        // Get public key from extension (normalize so tag/filter comparisons match)
        state.publicKey = normalizePubkey(await window.nostr.getPublicKey());

        // Check if extension supports NIP-44 (required for this app)
        if (!window.nostr.nip44 || !window.nostr.nip44.encrypt || !window.nostr.nip44.decrypt) {
            if (loginBtn) {
                loginBtn.disabled = false;
                loginBtn.textContent = 'Login with Nostr';
            }
            alert('Your Nostr extension does not support NIP-44 encryption/decryption.\n\n' +
                  'This app requires NIP-44 support for secure messaging.\n\n' +
                  'Please use an extension that supports NIP-44:\n' +
                  '• Alby (recommended) — https://getalby.com/\n' +
                  '• Or another extension with NIP-44 support\n\n' +
                  'After installing/updating, refresh this page.');
            return;
        }

        if (state.messageSubscription) {
            try {
                state.messageSubscription.close();
            } catch (e) {
                console.warn('Closing previous message subscription:', e);
            }
            state.messageSubscription = null;
        }
        if (state.pool) {
            stopIncrementalInboxSync();
            state.gapFillDebounceByConv.forEach((t) => clearTimeout(t));
            state.gapFillDebounceByConv.clear();
            state.gapFillLastRunMs.clear();
            state.conversationRepairRunning.clear();
            resetSessionSyncState();
            try {
                state.pool.destroy();
            } catch (e) {
                console.warn('Destroying previous relay pool:', e);
            }
        }
        stopIncrementalNip04Sync();
        state.lastInboxGiftWrapProcessedSec = 0;
        state.lastKind4ProcessedSec = 0;
        // enableReconnect: pool automatically re-establishes dropped WebSocket connections
        // and re-sends active subscriptions, covering desktop WiFi drops without manual catchup.
        state.pool = new SimplePool({ enableReconnect: true });

        // Bootstrap against defaults + relay-list indexers to discover our kind 10050.
        const bootstrapResults = await connectRelaySet(RELAY_URLS);

        // Full three-tier resolution: kind 10050 on current set → discovery relays → NIP-65 fallback.
        let ownInboxRelays = await resolveInboxRelays(state.publicKey);
        if (!ownInboxRelays.length) {
            console.warn('Inbox relays not found via kind 10050 or NIP-65 — using default relays. ' +
                'Go to Settings → DM Relays to configure your inbox relays.');
        }

        state.dmRelayUrls = ownInboxRelays.length ? [...new Set(ownInboxRelays)] : [...RELAY_URLS];
        // Persist so the next session can bootstrap kind 10050 discovery from the user's own relay.
        void idbPut('meta', { key: 'dmRelayUrls', value: state.dmRelayUrls }).catch(() => {});
        const additionalRelayUrls = state.dmRelayUrls.filter((url) => !RELAY_URLS.includes(url));
        const additionalResults = additionalRelayUrls.length ? await connectRelaySet(additionalRelayUrls) : [];
        const relayResults = [...bootstrapResults, ...additionalResults];
        const relayStatusByUrl = new Map(relayResults.map((r) => [r.url, r]));
        const inboxRelayStatuses = ownInboxRelays.length
            ? state.dmRelayUrls.map((url) => relayStatusByUrl.get(url) || { url, success: false })
            : [];

        document.getElementById('connectionSetup').style.display = 'none';
        document.getElementById('convTabs')?.removeAttribute('hidden');
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

        updateRelayStatusCard(bootstrapResults, inboxRelayStatuses);

        // Load persisted state from IndexedDB before showing conversations — instant display
        // for returning users without waiting for relay queries to complete.
        await loadStateFromDB(state.publicKey);
        await loadNip04StateFromDB(state.publicKey);
        updateConversationsList();

        // Refresh blossom server list from kind 10063 so upload order matches what the user
        // configured (potentially from another client), not just the stale IDB cache.
        void fetchKind10063Servers(state.publicKey).then((servers) => {
            if (servers.length) {
                state.blossomServers = servers;
                void idbPut('meta', { key: 'blossomServers', value: servers }).catch(() => {});
            }
        });

        setInboxLoading(true);
        await loadOwnCustomReactionSetFromNostr();

        // Live subscription first so new mail arrives while history is still decrypting.
        // History uses paginated querySync (relay result caps) + batched UI updates for mobile perf.
        subscribeToMessages();
        subscribeToNip04Messages();
        startIncrementalInboxSync();
        startIncrementalNip04Sync();
        updateSettingsSyncUiState();
        void fetchHistoricalGiftWraps().finally(() => {
            setInboxLoading(false);
            prefetchMissingConversationProfiles();
        });
        void loadHistoricalNip04Messages();

    } catch (error) {
        setInboxLoading(false);
        if (loginBtn) {
            loginBtn.disabled = false;
            loginBtn.textContent = 'Login with Nostr';
        }
        alert('Connection failed: ' + error.message);
        console.error(error);
    }
}

// Make functions available globally for onclick handlers
window.connectWithExtension = connectWithExtension;
window.sendMessage = sendMessage;
window.backToConversations = backToConversations;
window.switchConversationTab = switchConversationTab;

// Diagnostic helper — run __bullishDiag() in the browser console to inspect sync state
window.__bullishDiag = () => {
    const convSummary = {};
    for (const [pk, msgs] of Object.entries(state.conversations)) {
        convSummary[pk.slice(0, 8)] = msgs.length;
    }
    return {
        conversationCount: Object.keys(state.conversations).length,
        conversations: convSummary,
        seenWrapCount: state.seenGiftWrapEventIds.size,
        seenRumorCount: state.seenRumorIds.size,
        cursor: state.lastInboxGiftWrapProcessedSec,
        cursorDate: state.lastInboxGiftWrapProcessedSec > 0
            ? new Date(state.lastInboxGiftWrapProcessedSec * 1000).toISOString()
            : 'none',
        dbAvailable: !!state.db,
        dmRelays: [...state.dmRelayUrls],
        telemetry: { ...state.syncTelemetry },
    };
};

// Initialize DOM event listeners when DOM is ready
document.addEventListener('DOMContentLoaded', function() {
    void initDB();

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
            const cs = window.getComputedStyle(this);
            const lineHeight = parseFloat(cs.lineHeight) || 20;
            const padTop = parseFloat(cs.paddingTop) || 0;
            const padBottom = parseFloat(cs.paddingBottom) || 0;
            const maxLines = isMobileLayout() ? 6 : 2;
            const maxHeight = lineHeight * maxLines + padTop + padBottom;
            this.style.height = Math.min(this.scrollHeight, maxHeight) + 'px';
        });

        // iOS Safari keeps the page scrolled after keyboard dismissal; reset it.
        messageInput.addEventListener('blur', function() {
            setTimeout(() => window.scrollTo(0, 0), 150);
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

    const imageFileInput = document.getElementById('imageFileInput');
    const imageUploadBtn = document.getElementById('imageUploadBtn');
    if (imageUploadBtn && imageFileInput) {
        imageUploadBtn.addEventListener('click', () => imageFileInput.click());
        imageFileInput.addEventListener('change', async () => {
            const file = imageFileInput.files?.[0];
            if (file) {
                await sendImageMessage(file);
                imageFileInput.value = '';
            }
        });
    }

    const imagePreviewRemove = document.getElementById('chatImagePreviewRemove');
    if (imagePreviewRemove) {
        imagePreviewRemove.addEventListener('click', () => clearPendingImage());
    }

    document.addEventListener('visibilitychange', () => {
        if (document.visibilityState === 'visible') {
            scheduleMobileCatchup('visibility-resume');
        }
    });
    window.addEventListener('online', () => {
        scheduleMobileCatchup('network-online');
    });
});
