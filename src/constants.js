// Relay URLs to connect to
export const RELAY_URLS = [
    'wss://relay.0xchat.com',
    'wss://relay.damus.io',
    'wss://relay.primal.net',
    'wss://nos.lol'
];

/** Relay-list indexers used for NIP-17/NIP-65 discovery when kind 10050 is not on default relays. */
export const DISCOVERY_RELAYS = ['wss://purplepag.es'];

export const DEFAULT_QUICK_REACTIONS = ['🤙', '💜', '👍', '😂', '🚀'];
export const DEFAULT_EXTRA_REACTIONS = ['🔥', '👏', '🙏', '🎉', '👀', '💯', '🤯', '🥲', '😎', '🤔'];

export const CUSTOM_REACTION_SET_KIND = 30030;
export const CUSTOM_REACTION_SET_D_TAG = 'bullishchat-reaction-set';
/** NIP-30 does not define a max; this caps kind 30030 size for UI and relay friendliness. */
export const MAX_CUSTOM_REACTION_EMOJIS = 256;

export const EMOJI_DISCOVERY_PAGE_LIMIT = 500;
export const EMOJI_DISCOVERY_MAX_PAGES = 10;

export const LIGHTNING_INVOICE_RE = /(lightning:)?(ln(?:bc|tb|bcrt|sb)[0-9a-z]+)/i;
/** Detect bare http(s) URLs in message text for links / inline images (DOM-built, no HTML injection). */
export const HTTP_URL_IN_TEXT_RE = /\bhttps?:\/\/[^\s<>"'`]+/gi;

export const CONVERSATION_REPAIR_LOOKBACK_SECS = 14 * 24 * 60 * 60;
export const CONVERSATION_REPAIR_LIMIT = 1200;
export const CONVERSATION_REPAIR_COOLDOWN_MS = 15000;
/** Paginated repair: one REQ often caps below total backlog (mobile + multi-relay). */
export const REPAIR_MAX_PAGES_DEFAULT = 8;
export const REPAIR_MAX_PAGES_DEEP = 14;
export const REPAIR_PAGE_LIMIT_DEEP = 1500;

export const INCREMENTAL_INBOX_INTERVAL_MS = 45_000;
/** NIP-59 randomizes gift-wrap created_at up to 2 days into the past.
 *  Amethyst uses 2 days; Gossip uses 7 days. Use 2 days so backdated
 *  wraps are never below our since cursor. */
export const INCREMENTAL_INBOX_OVERLAP_SECS = 2 * 24 * 60 * 60;
export const INCREMENTAL_INBOX_PAGE_LIMIT = 400;
export const INCREMENTAL_INBOX_MAX_PAGES = 2;

export const GAP_FILL_DEBOUNCE_MS = 450;
export const GAP_FILL_COOLDOWN_MS = 8000;
export const GAP_FILL_MAX_PAGES = 5;

export const STALE_PENDING_REACTION_MS = 90_000;

/** Nostr Archives search suggest endpoint. */
export const NOSTR_ARCHIVES_SEARCH_SUGGEST_URL = 'https://api.nostrarchives.com/v1/search/suggest';
export const NOSTR_ARCHIVES_PROFILES_METADATA_URL = 'https://api.nostrarchives.com/v1/profiles/metadata';
export const PROFILE_METADATA_BATCH_SIZE = 100;

export const IDB_NAME = 'bullishchat';
export const IDB_VERSION = 3;

export const NIP04_INCREMENTAL_INTERVAL_MS = 45_000;
export const NIP04_HISTORY_LOOKBACK_SECS = 180 * 24 * 60 * 60;

/** NIP-59 backdating means we need at least a 2-day overlap on startup to avoid missing
 *  messages whose created_at was randomised below the stored cursor. */
export const STARTUP_HISTORY_OVERLAP_SECS = 2 * 24 * 60 * 60;

export const DEFAULT_BLOSSOM_SERVERS = [
    'https://blossom.band',
    'https://blossom.primal.net'
];
export const NOSTR_BUILD_UPLOAD_URL = 'https://nostr.build/api/v2/upload/files';
export const MAX_IMAGE_UPLOAD_BYTES = 25 * 1024 * 1024;
export const BLOSSOM_SERVER_LIST_KIND = 10063;

/** Lowercase hex pubkey for stable Map keys and comparisons */
export function normalizePubkey(pk) {
    if (!pk || typeof pk !== 'string') return '';
    return pk.toLowerCase().replace(/[^0-9a-f]/g, '').slice(0, 64);
}
