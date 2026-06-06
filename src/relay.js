import { state } from './state.js';
import { RELAY_URLS, DISCOVERY_RELAYS, normalizePubkey } from './constants.js';
import { idbPut } from './db.js';

export async function nostrAuthHandler(authEventTemplate) {
    if (!window.nostr?.signEvent) throw new Error('NIP-07 signer not available for relay AUTH');
    return window.nostr.signEvent(authEventTemplate);
}

/** Kind 10050: preferred relays to receive NIP-17 gift wraps (NIP-17 publishing + our subscription) */
export async function fetchKind10050Relays(authorPubkey, options = {}) {
    try {
        const queryRelays = options.relays?.length
            ? [...new Set(options.relays)]
            : [...new Set([...(state.dmRelayUrls?.length ? state.dmRelayUrls : []), ...RELAY_URLS])];
        if (options.ensureConnections) {
            await connectRelaySet(queryRelays);
        }
        const events = await state.pool.querySync(
            queryRelays,
            { kinds: [10050], authors: [authorPubkey], limit: 8 },
            { maxWait: options.maxWait ?? 9000, onauth: nostrAuthHandler }
        );
        const ev = (events || []).sort((a, b) => (b.created_at || 0) - (a.created_at || 0))[0];
        if (!ev?.tags?.length) return [];
        return ev.tags.filter((t) => t[0] === 'relay' && typeof t[1] === 'string' && t[1].length > 0).map((t) => t[1]);
    } catch (e) {
        console.warn('fetchKind10050Relays failed:', e);
        return [];
    }
}

/**
 * NIP-65 (kind 10002) inbox relays for a pubkey — used as a fallback when kind 10050
 * is not found. Coracle/Welshman and Amethyst both merge NIP-65 inbox relays with
 * kind 10050 when resolving where to publish DMs.
 */
export async function fetchNip65InboxRelays(authorPubkey, queryRelays) {
    try {
        const relays = queryRelays?.length
            ? [...new Set(queryRelays)]
            : [...new Set([...(state.dmRelayUrls?.length ? state.dmRelayUrls : []), ...RELAY_URLS, ...DISCOVERY_RELAYS])];
        const events = await state.pool.querySync(
            relays,
            { kinds: [10002], authors: [authorPubkey], limit: 3 },
            { maxWait: 7000, onauth: nostrAuthHandler }
        );
        const ev = (events || []).sort((a, b) => (b.created_at || 0) - (a.created_at || 0))[0];
        if (!ev?.tags?.length) return [];
        // ['r', url] = both read+write; ['r', url, 'read'] = inbox only; ['r', url, 'write'] = skip
        return ev.tags
            .filter((t) => t[0] === 'r' && typeof t[1] === 'string' && t[1].length && t[2] !== 'write')
            .map((t) => t[1]);
    } catch (e) {
        console.warn('fetchNip65InboxRelays failed:', e);
        return [];
    }
}

/**
 * Resolve inbox relays for a pubkey with a three-tier fallback chain used by all
 * major NIP-17 clients (Amethyst, Coracle, 0xchat):
 *   1. kind 10050 on current relay set
 *   2. kind 10050 on relay-list indexers (purplepag.es)
 *   3. kind 10002 NIP-65 inbox relays as last resort
 */
export async function resolveInboxRelays(authorPubkey) {
    // 1. Try kind 10050 on current relay set
    let relays = await fetchKind10050Relays(authorPubkey);
    if (relays.length) return relays;

    // 2. Try kind 10050 on relay-list indexers
    const discoverySet = [...new Set([...DISCOVERY_RELAYS, ...RELAY_URLS])];
    relays = await fetchKind10050Relays(authorPubkey, { relays: discoverySet, maxWait: 8000 });
    if (relays.length) {
        console.info(`resolveInboxRelays: found kind 10050 via discovery relays for ${authorPubkey.slice(0, 8)}`);
        return relays;
    }

    // 3. Fall back to NIP-65 (kind 10002) inbox relays
    relays = await fetchNip65InboxRelays(authorPubkey, discoverySet);
    if (relays.length) {
        console.info(`resolveInboxRelays: using NIP-65 inbox relays as fallback for ${authorPubkey.slice(0, 8)}`);
    }
    return relays;
}

/** Read from both default + discovered inbox relays to reduce missed events on flaky/mobile sockets. */
export function getReadRelayUrlsUnsorted() {
    return [...new Set([...(state.dmRelayUrls || []), ...RELAY_URLS])];
}

export function recordRelayReadStat(url, ok, latencyMs = 0) {
    const u = String(url || '');
    if (!u) return;
    let s = state.relayReadStats.get(u);
    if (!s) {
        s = { ok: 0, fail: 0, lastMs: 500 };
        state.relayReadStats.set(u, s);
    }
    if (ok) {
        s.ok += 1;
        s.lastMs = Math.max(1, latencyMs || 1);
    } else {
        s.fail += 1;
    }
}

/** Prefer relays with higher recent success rate and lower last connect latency. */
export function sortRelaysForRead(urls) {
    const arr = [...new Set(urls)];
    return arr.sort((a, b) => {
        const sa = state.relayReadStats.get(a) || { ok: 0, fail: 0, lastMs: 500 };
        const sb = state.relayReadStats.get(b) || { ok: 0, fail: 0, lastMs: 500 };
        const na = sa.ok + sa.fail;
        const nb = sb.ok + sb.fail;
        const ra = na ? sa.ok / na : 0.5;
        const rb = nb ? sb.ok / nb : 0.5;
        if (rb !== ra) {
            return rb - ra;
        }
        return sa.lastMs - sb.lastMs;
    });
}

export function getReadRelayUrls() {
    return sortRelaysForRead(getReadRelayUrlsUnsorted());
}

/** Connects the pool to the exact relay set and returns statuses. */
export async function connectRelaySet(relays) {
    const statuses = await Promise.all(
        relays.map(async (url) => {
            const t0 = Date.now();
            try {
                await state.pool.ensureRelay(url);
                const ms = Date.now() - t0;
                recordRelayReadStat(url, true, ms);
                return { url, success: true };
            } catch (err) {
                recordRelayReadStat(url, false, 0);
                console.warn('Failed to connect to relay:', url, err);
                return { url, success: false };
            }
        })
    );
    return statuses;
}

// Generate random timestamp within 2 days in the past
export function getRandomPastTimestamp() {
    const now = Math.floor(Date.now() / 1000);
    const twoDaysAgo = now - (2 * 24 * 60 * 60);
    return twoDaysAgo + Math.floor(Math.random() * (2 * 24 * 60 * 60));
}
