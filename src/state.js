import { RELAY_URLS, DEFAULT_BLOSSOM_SERVERS } from './constants.js';

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
    /** Skip re-touching conversation-list DOM when a poll finds nothing actually changed. */
    conversationsListFingerprint: '',
    nip04ConversationsListFingerprint: '',
    /** Which tab ('nip04' or not) the conversation list was last actually rendered for — lets a
     *  tab switch force a real render even when the fingerprint is unchanged. */
    lastRenderedConversationsTab: null,
    /** Skip rebuilding the open message thread (and closing any open reaction picker) when a poll
     *  re-renders the active chat but nothing in it actually changed. */
    displayedMessagesFingerprint: '',
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
    /** Timestamp of the last transient (network/timeout) profile fetch failure per pubkey, so
     *  fetchUserProfile can cool down retries without permanently caching a bad "empty" result. */
    profileFetchFailedAt: new Map(),
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
    blossomServers: [...DEFAULT_BLOSSOM_SERVERS],
    settingsBlossomDraft: [],
    pendingImageUrl: null,
    pendingImageObjectUrl: null,
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
    /** 'nip17' | 'nip04' — which tab is shown in the conversation list */
    activeConversationTab: 'nip17',
    /** Whether the NIP-04 tab should show an unread dot */
    nip04HasUnread: false,
    /** Pubkeys with unread NIP-17 messages (cleared when conversation is opened) */
    unreadNip17: new Set(),
    /** Pubkeys with unread NIP-04 messages (cleared when conversation is opened) */
    unreadNip04: new Set(),
    /** Unix seconds when this session started — used to skip marking historical loads as unread */
    sessionStartedAt: Math.floor(Date.now() / 1000),
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
    /** Pubkeys muted via the NIP-51 kind 10000 mute list — hidden from both conversation tabs. */
    mutedPubkeys: new Set(),
    /** Verbatim tags of our newest kind 10000 event (may hold plaintext p/word/t/e entries from other clients). */
    muteListPublicTags: [],
    /** Decrypted private items from the kind 10000 content (verbatim; non-p entries preserved on publish). */
    muteListPrivateItems: [],
    /** Original kind 10000 ciphertext — republished untouched if we couldn't decrypt it. */
    muteListRawContent: '',
    /** True when the kind 10000 content exists but could not be decrypted (blocks private-side edits). */
    muteListContentUnreadable: false,
    /** Newest own kind 10050/10063 events — saves merge non-relay/non-server tags back in. */
    ownKind10050Event: null,
    ownKind10063Event: null,
    /** Newest own kind 10030 (user emoji list) — saves preserve its 'a' refs and content. */
    ownKind10030Event: null,
    /** Decrypted private items from the 10030 content (verbatim; non-emoji entries preserved on save). */
    ownKind10030PrivateItems: [],
    /** True when the 10030 content exists but could not be decrypted (blocks private-side edits). */
    ownKind10030ContentUnreadable: false,
};
