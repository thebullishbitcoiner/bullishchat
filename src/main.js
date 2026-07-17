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
    initViewJsonModal,
    initMessageMenus,
    isMobileLayout,
    setMobileChatPanel,
    backToConversations,
    displayMessages,
    updateChatHeader,
    updateRelayStatusCard,
    switchConversationTab
} from './ui.js';
import { initSettingsUi, loadOwnCustomReactionSetFromNostr } from './settings.js';
import { loadMuteListFromNostr } from './mute.js';

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

        // Connect the default relay set only — kind 10050/NIP-65 inbox relay discovery is
        // slow (multi-relay EOSE waits) and runs in the background so it doesn't block login.
        const bootstrapResults = await connectRelaySet(RELAY_URLS);

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

        updateRelayStatusCard(bootstrapResults, []);

        // Load persisted state from IndexedDB before showing conversations — instant display
        // for returning users without waiting for relay queries to complete. This also restores
        // dmRelayUrls discovered in a prior session, so subscriptions below can already target
        // the user's real inbox relay instead of only the app defaults.
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

        // Refresh the mute list from kind 10000 (may include mutes made on another device/client
        // since our local IDB cache was written); re-render once resolved so any newly-muted
        // conversation that slipped in from the DB cache is dropped from the list.
        void loadMuteListFromNostr().then(() => updateConversationsList());

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

        // Resolve authoritative inbox relays (kind 10050, falling back to NIP-65) in the
        // background. If discovery finds a relay set we weren't already using, connect to
        // it and restart the live subscriptions so messages there aren't missed.
        void refreshInboxRelaysInBackground(bootstrapResults);

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

/**
 * Runs after login without blocking the UI. Resolves the user's real inbox relays
 * (kind 10050, falling back to NIP-65) and, if that differs from what we're already
 * using (defaults or a prior-session cache), connects to it and restarts the live
 * subscriptions so new messages on that relay aren't missed for up to a full
 * incremental-sync interval.
 */
async function refreshInboxRelaysInBackground(bootstrapResults) {
    try {
        const discovered = await resolveInboxRelays(state.publicKey);
        if (!discovered.length) {
            console.warn('Inbox relays not found via kind 10050 or NIP-65 — using default relays. ' +
                'Go to Settings → DM Relays to configure your inbox relays.');
            return;
        }

        const newSet = [...new Set(discovered)];
        // Subscriptions were opened against state.dmRelayUrls as it stood at login (defaults,
        // or a prior-session cache) — only restart them if discovery actually changed that set.
        const subscriptionRelaysChanged = newSet.length !== state.dmRelayUrls.length ||
            !newSet.every((url) => state.dmRelayUrls.includes(url));

        state.dmRelayUrls = newSet;
        // Persist so the next session can skip straight to the user's own relay.
        void idbPut('meta', { key: 'dmRelayUrls', value: state.dmRelayUrls }).catch(() => {});

        const additionalRelayUrls = newSet.filter((url) => !RELAY_URLS.includes(url));
        const additionalResults = additionalRelayUrls.length ? await connectRelaySet(additionalRelayUrls) : [];
        // Always refresh the card so the "Inbox relays" section reflects the resolved set,
        // even when it matches what we already had (e.g. a returning user's cached relays).
        const relayStatusByUrl = new Map([...bootstrapResults, ...additionalResults].map((r) => [r.url, r]));
        const inboxRelayStatuses = newSet.map((url) => relayStatusByUrl.get(url) || { url, success: false });
        updateRelayStatusCard(bootstrapResults, inboxRelayStatuses);

        if (!subscriptionRelaysChanged) return;

        if (state.messageSubscription) {
            try {
                state.messageSubscription.close();
            } catch (e) {
                console.warn('Closing message subscription for inbox relay refresh:', e);
            }
        }
        if (state.kind4Subscription) {
            for (const sub of state.kind4Subscription) {
                try {
                    sub.close();
                } catch (e) {
                    console.warn('Closing NIP-04 subscription for inbox relay refresh:', e);
                }
            }
        }
        subscribeToMessages();
        subscribeToNip04Messages();
    } catch (e) {
        console.warn('Background inbox relay resolution failed:', e);
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
    initViewJsonModal();
    initMessageMenus();

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
