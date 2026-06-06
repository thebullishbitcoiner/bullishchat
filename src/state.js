import { RELAY_URLS } from './constants.js';

export const state = {
    pool: null,
    publicKey: null,
    conversations: {},
    currentChat: null,
    userProfiles: {},
    messageSubscription: null,
    /** Relays used for DM subscribe/publish: default list plus our kind 10050 inbox relays after connect */
    dmRelayUrls: [...RELAY_URLS],
    /** Dedupe kind 1059 events across historical query + live subscription (same id from many relays) */
    seenGiftWrapEventIds: new Set(),
    /** Avoid repeatedly trying broken image URLs (prevents avatar flash/retry loops). */
    brokenAvatarUrls: new Set(),
    /** Keep stable DOM rows for conversation list to avoid avatar remount flicker. */
    conversationItemEls: new Map(),
    /** De-dupe rumors that can arrive via sender/receiver copies across relays. */
    seenRumorIds: new Set(),
    /** Reactions that arrive before their target message. */
    pendingReactionsByMessageId: new Map(),
    /** First time we queued a reaction whose target message is still missing (for stale gap-fill). */
    pendingReactionFirstSeen: new Map(),
    /** Lightweight connect / read health for ordering relay lists. */
    relayReadStats: new Map(),
    syncTelemetry: {
        giftWrapDecryptFail: 0,
        sealDecryptFail: 0,
        rumorUnsupported: 0,
        gapFillRuns: 0,
        manualSyncRuns: 0,
        querySyncCalls: 0,
        querySyncErrors: 0,
        querySyncMsTotal: 0,
        ingestEventsReceived: 0,
        ingestHandlerErrors: 0,
        incrementalRuns: 0,
        repairRuns: 0
    },
    manualInboxSyncInFlight: false,
    /** Blob URLs for decrypted kind-15 previews — revoked when the message list re-renders. */
    activeMessageBlobUrls: new Set(),
    profileFetchInFlight: new Map(),
    conversationRepairLastRunMs: new Map(),
    /** Per-thread repair so opening chat B is not blocked by chat A. */
    conversationRepairRunning: new Set(),
    lastInboxGiftWrapProcessedSec: 0,
    incrementalInboxTimerId: null,
    incrementalInboxInFlight: false,
    gapFillDebounceByConv: new Map(),
    gapFillLastRunMs: new Map(),
    isInboxLoading: false,
    settingsRelayDraft: [],
    customReactionEmojiSet: [],
    customReactionEmojiUrlMap: {},
    /** Latest merged catalog from relay discovery (filter in UI without re-fetching). */
    emojiDiscoverCatalog: [],
    /** When set, discover UI shows one catalog entry for per-emoji add. */
    emojiDiscoverDetailSet: null,
    emojiDiscoverInFlight: false,
    /** True after the first Discover query this app session (query runs once until reload). */
    emojiDiscoverQueriedThisModalOpen: false,
    emojiDiscoverSearchDebounce: null,
    settingsEmojiDraftSet: [],
    mobileCatchupTimer: null,
    /** NIP-04 (kind 4) conversations, keyed by peer pubkey — separate from NIP-17 */
    nip04Conversations: {},
    seenKind4EventIds: new Set(),
    lastKind4ProcessedSec: 0,
    /** Stable DOM rows for NIP-04 conversation list (avoids avatar remount flicker) */
    nip04ConversationItemEls: new Map(),
    kind4Subscription: null,
    /** 'nip17' | 'nip04' | null — drives send path and which message store renders */
    currentChatProtocol: null,
    incrementalNip04TimerId: null,
    db: null,
    profileSearchAbort: null,
    profileSearchDebounceTimer: null,
    profileSearchSerial: 0,
    lastProfileSearchRequestMs: 0,
    conversationsListUpdateQueued: false,
    chatHeaderUpdateQueued: false,
    activeChatRenderTimer: null,
    activeChatRenderPubkey: null,
    activeChatRenderNeedsHeader: false,
};
