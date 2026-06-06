import { state } from './state.js';
import {
    normalizePubkey,
    STALE_PENDING_REACTION_MS,
    INCREMENTAL_INBOX_INTERVAL_MS,
    INCREMENTAL_INBOX_OVERLAP_SECS,
    INCREMENTAL_INBOX_PAGE_LIMIT,
    INCREMENTAL_INBOX_MAX_PAGES,
    CONVERSATION_REPAIR_LOOKBACK_SECS,
    CONVERSATION_REPAIR_LIMIT,
    CONVERSATION_REPAIR_COOLDOWN_MS,
    REPAIR_MAX_PAGES_DEFAULT,
    REPAIR_MAX_PAGES_DEEP,
    REPAIR_PAGE_LIMIT_DEEP,
    GAP_FILL_DEBOUNCE_MS,
    GAP_FILL_COOLDOWN_MS,
    GAP_FILL_MAX_PAGES,
    STARTUP_HISTORY_OVERLAP_SECS,
    NIP04_INCREMENTAL_INTERVAL_MS,
    NIP04_HISTORY_LOOKBACK_SECS
} from './constants.js';
import { idbPut, dbSaveNip04Cursor } from './db.js';
import {
    getReadRelayUrls,
    getReadRelayUrlsUnsorted,
    sortRelaysForRead,
    connectRelaySet,
    nostrAuthHandler
} from './relay.js';
import { prefetchMissingConversationProfiles } from './profile.js';
import { getConversationFingerprint } from './messages.js';

export function resetSessionSyncState() {
    for (const k of Object.keys(state.syncTelemetry)) {
        if (typeof state.syncTelemetry[k] === 'number') {
            state.syncTelemetry[k] = 0;
        }
    }
    state.relayReadStats.clear();
    state.pendingReactionFirstSeen.clear();
}

export function logSyncTelemetrySnapshot() {
    const relaySnapshot = {};
    for (const [url, s] of state.relayReadStats) {
        const n = s.ok + s.fail;
        relaySnapshot[url] = {
            ok: s.ok,
            fail: s.fail,
            successRate: n ? Number((s.ok / n).toFixed(3)) : null,
            lastConnectMs: s.lastMs
        };
    }
    const avgMs = state.syncTelemetry.querySyncCalls
        ? Math.round(state.syncTelemetry.querySyncMsTotal / state.syncTelemetry.querySyncCalls)
        : 0;
    console.info('[bullishchat sync telemetry]', {
        ...state.syncTelemetry,
        avgQuerySyncMs: avgMs,
        pendingOrphanReactionTargets: state.pendingReactionsByMessageId.size,
        pendingFirstSeenTracked: state.pendingReactionFirstSeen.size,
        relayReadHealth: relaySnapshot
    });
}

export function kickStalePendingReactions() {
    const now = Date.now();
    const convs = new Set();
    for (const [msgId, firstSeen] of state.pendingReactionFirstSeen) {
        if (now - firstSeen < STALE_PENDING_REACTION_MS) {
            continue;
        }
        const list = state.pendingReactionsByMessageId.get(msgId);
        if (!list?.length) {
            state.pendingReactionFirstSeen.delete(msgId);
            continue;
        }
        for (const p of list) {
            if (p?.conversationPubkey) {
                convs.add(normalizePubkey(p.conversationPubkey));
            }
        }
    }
    for (const pk of convs) {
        scheduleGapFillForConversation(pk);
    }
}

export function noteInboxGiftWrapProcessed(createdAt) {
    const t = typeof createdAt === 'number' && createdAt > 0 ? createdAt : 0;
    if (t > state.lastInboxGiftWrapProcessedSec) {
        state.lastInboxGiftWrapProcessedSec = t;
        // Lazy import to avoid circular with db (already imported above — actually db is imported directly)
        idbPut('meta', { key: 'lastInboxGiftWrapProcessedSec', value: t }).catch((e) =>
            console.warn('DB: save cursor failed:', e)
        );
    }
}

/**
 * Page kind-1059 inbox queries backward in time (until cursor) so we are not limited to one relay page.
 * @param {string[]} readRelays
 * @param {(until?: number) => object} buildFilter — return filter without `limit`
 * @param {{ pageLimit: number, maxPages: number, maxWaitBase: number, suppressUi?: boolean }} opts
 */
export async function ingestPagedGiftWraps(readRelays, buildFilter, opts) {
    const { pageLimit, maxPages, maxWaitBase, suppressUi = true } = opts;
    const ordered = sortRelaysForRead([...new Set(readRelays)]);
    let until;
    for (let page = 0; page < maxPages; page++) {
        const filter = buildFilter(until);
        filter.limit = pageLimit;
        let baseMw = Math.min(65000, maxWaitBase + ordered.length * 3500);
        let events;
        for (let attempt = 0; attempt < 2; attempt++) {
            const maxWait = attempt === 0 ? baseMw : Math.min(65000, Math.floor(baseMw * 1.85));
            state.syncTelemetry.querySyncCalls += 1;
            const t0 = Date.now();
            try {
                events = await state.pool.querySync(ordered, filter, { maxWait, onauth: nostrAuthHandler });
                state.syncTelemetry.querySyncMsTotal += Date.now() - t0;
                break;
            } catch (qe) {
                state.syncTelemetry.querySyncErrors += 1;
                if (attempt === 1) {
                    console.warn(
                        'ingestPagedGiftWraps: page query failed after 2 attempts — some messages may be missing. Check relay connectivity.',
                        qe
                    );
                    events = [];
                }
            }
        }
        if (!events?.length) {
            break;
        }
        state.syncTelemetry.ingestEventsReceived += events.length;
        events.sort((a, b) => a.created_at - b.created_at);
        for (const ev of events) {
            try {
                // Lazy import to avoid circular dependency
                const { handleGiftWrappedMessage } = await import('./messages.js');
                await handleGiftWrappedMessage(ev, { suppressUi });
            } catch (err) {
                state.syncTelemetry.ingestHandlerErrors += 1;
                console.warn('ingestPagedGiftWraps: handle error:', err);
            }
        }
        if (events.length < pageLimit) {
            break;
        }
        until = events[0].created_at - 1;
    }
}

export function stopIncrementalInboxSync() {
    if (state.incrementalInboxTimerId) {
        clearInterval(state.incrementalInboxTimerId);
        state.incrementalInboxTimerId = null;
    }
}

export function startIncrementalInboxSync() {
    stopIncrementalInboxSync();
    state.incrementalInboxTimerId = setInterval(() => {
        void runIncrementalInboxSync();
    }, INCREMENTAL_INBOX_INTERVAL_MS);
}

export async function runIncrementalInboxSync() {
    if (!state.pool || !state.publicKey || state.incrementalInboxInFlight) {
        return;
    }
    state.incrementalInboxInFlight = true;
    state.syncTelemetry.incrementalRuns += 1;
    try {
        const readRelays = getReadRelayUrls();
        const nowSec = Math.floor(Date.now() / 1000);
        const baseline = state.lastInboxGiftWrapProcessedSec > 0 ? state.lastInboxGiftWrapProcessedSec : nowSec - 24 * 60 * 60;
        const since = Math.max(0, baseline - INCREMENTAL_INBOX_OVERLAP_SECS);
        await ingestPagedGiftWraps(
            readRelays,
            (until) => {
                const f = { kinds: [1059], '#p': [state.publicKey], since };
                if (until !== undefined) {
                    f.until = until;
                }
                return f;
            },
            {
                pageLimit: INCREMENTAL_INBOX_PAGE_LIMIT,
                maxPages: INCREMENTAL_INBOX_MAX_PAGES,
                maxWaitBase: 9000,
                suppressUi: true
            }
        );
        const { updateConversationsList } = await import('./ui.js');
        updateConversationsList();
        if (state.currentChat) {
            const { queueActiveChatRender } = await import('./queue.js');
            queueActiveChatRender(state.currentChat, { header: true });
        }
    } catch (err) {
        console.warn('Incremental inbox sync failed:', err);
    } finally {
        state.incrementalInboxInFlight = false;
        kickStalePendingReactions();
    }
}

export function conversationHasPendingReactions(conversationPubkey) {
    const pk = normalizePubkey(conversationPubkey);
    for (const [, list] of state.pendingReactionsByMessageId) {
        if (!Array.isArray(list)) {
            continue;
        }
        if (list.some((p) => p && normalizePubkey(p.conversationPubkey) === pk)) {
            return true;
        }
    }
    return false;
}

export function scheduleGapFillForConversation(conversationPubkey) {
    const pk = normalizePubkey(conversationPubkey);
    const prev = state.gapFillDebounceByConv.get(pk);
    if (prev) {
        clearTimeout(prev);
    }
    state.gapFillDebounceByConv.set(
        pk,
        setTimeout(() => {
            state.gapFillDebounceByConv.delete(pk);
            void runGapFillForConversation(pk);
        }, GAP_FILL_DEBOUNCE_MS)
    );
}

export async function runGapFillForConversation(conversationPubkey) {
    if (!state.pool || !state.publicKey || !conversationPubkey) {
        return;
    }
    const pk = normalizePubkey(conversationPubkey);
    if (!conversationHasPendingReactions(pk)) {
        return;
    }
    const now = Date.now();
    if (now - (state.gapFillLastRunMs.get(pk) || 0) < GAP_FILL_COOLDOWN_MS) {
        return;
    }
    state.gapFillLastRunMs.set(pk, now);
    state.syncTelemetry.gapFillRuns += 1;

    const readRelays = getReadRelayUrls();
    const since = Math.floor(Date.now() / 1000) - CONVERSATION_REPAIR_LOOKBACK_SECS;
    try {
        await ingestPagedGiftWraps(
            readRelays,
            (until) => {
                const f = { kinds: [1059], '#p': [state.publicKey], since };
                if (until !== undefined) {
                    f.until = until;
                }
                return f;
            },
            {
                pageLimit: CONVERSATION_REPAIR_LIMIT,
                maxPages: GAP_FILL_MAX_PAGES,
                maxWaitBase: 14000,
                suppressUi: true
            }
        );
    } catch (err) {
        console.warn('Gap-fill gift wrap ingest failed:', err);
    }

    const { updateConversationsList, displayMessages, updateChatHeader } = await import('./ui.js');
    updateConversationsList();
    if (state.currentChat === pk) {
        displayMessages(pk);
        updateChatHeader(pk);
    }
}

/** Pull stored kind 1059 from relays (paginated: many relays cap events per REQ). */
export async function fetchHistoricalGiftWraps(options = {}) {
    if (!state.pool || !state.publicKey) return;

    const readRelays = getReadRelayUrls();
    const pageLimit = 500;
    const manual = Boolean(options.manual);
    const maxPages = manual ? 55 : 40;
    const maxWaitBase = manual ? 35000 : 20000;
    let until;

    // On startup with a persisted cursor: only fetch events since the last session
    // (plus a 1-day overlap to catch delayed relay delivery). Manual sync always
    // fetches the full history to repair any gaps.
    const sinceCursor =
        !manual && state.lastInboxGiftWrapProcessedSec > 0
            ? state.lastInboxGiftWrapProcessedSec - STARTUP_HISTORY_OVERLAP_SECS
            : undefined;

    try {
        for (let page = 0; page < maxPages; page++) {
            const filter = {
                kinds: [1059],
                '#p': [state.publicKey],
                limit: pageLimit
            };
            if (sinceCursor !== undefined) {
                filter.since = sinceCursor;
            }
            if (until !== undefined) {
                filter.until = until;
            }

            let baseMw = Math.min(
                manual ? 90000 : 65000,
                maxWaitBase + readRelays.length * (manual ? 8000 : 6000)
            );
            let events;
            for (let attempt = 0; attempt < 2; attempt++) {
                const maxWait = attempt === 0 ? baseMw : Math.min(manual ? 90000 : 65000, Math.floor(baseMw * 1.85));
                state.syncTelemetry.querySyncCalls += 1;
                const t0 = Date.now();
                try {
                    events = await state.pool.querySync(readRelays, filter, { maxWait, onauth: nostrAuthHandler });
                    state.syncTelemetry.querySyncMsTotal += Date.now() - t0;
                    break;
                } catch (qe) {
                    state.syncTelemetry.querySyncErrors += 1;
                    if (attempt === 1) {
                        console.warn('Historical gift wrap querySync failed after retry:', qe);
                        events = [];
                    }
                }
            }
            if (!events?.length) {
                break;
            }

            state.syncTelemetry.ingestEventsReceived += events.length;
            events.sort((a, b) => a.created_at - b.created_at);
            const oldest = events[0].created_at;

            for (const ev of events) {
                try {
                    const { handleGiftWrappedMessage } = await import('./messages.js');
                    await handleGiftWrappedMessage(ev, { suppressUi: true });
                } catch (err) {
                    state.syncTelemetry.ingestHandlerErrors += 1;
                    console.error('Error handling historical gift wrap:', err);
                }
            }

            if (events.length < pageLimit) {
                break;
            }
            until = oldest - 1;
        }
    } catch (err) {
        console.warn('Historical gift wrap querySync failed:', err);
    }

    const { updateConversationsList, displayMessages, updateChatHeader } = await import('./ui.js');
    updateConversationsList();
    if (state.currentChat) {
        displayMessages(state.currentChat);
        updateChatHeader(state.currentChat);
    }
    prefetchMissingConversationProfiles();
}

/**
 * Repair fetch when opening a thread: paginated kind-1059 backfill so we are not limited to one relay response page.
 * @param {{ deep?: boolean, force?: boolean }} [options] — deep: more pages / larger page size; force: bypass cooldown (manual sync)
 *
 * NOTE — inbox-wide filter by design: NIP-17 kind 1059 gift wraps use an ephemeral sender
 * pubkey, so the only reliable relay filter is `#p: [ourPubkey]` (the whole inbox). There is
 * no protocol-level way to request only wraps from a specific conversation peer. Each repair
 * run therefore re-ingests the full inbox window; already-seen wrap IDs are skipped immediately
 * via seenGiftWrapEventIds / IndexedDB, so the actual decryption cost is bounded to truly new events.
 */
export async function fetchConversationRepair(conversationPubkey, options = {}) {
    if (!state.pool || !state.publicKey || !conversationPubkey) {
        return;
    }
    const pk = normalizePubkey(conversationPubkey);
    if (state.conversationRepairRunning.has(pk)) {
        return;
    }

    const now = Date.now();
    const last = state.conversationRepairLastRunMs.get(pk) || 0;
    if (!options.force && now - last < CONVERSATION_REPAIR_COOLDOWN_MS) {
        return;
    }
    state.conversationRepairLastRunMs.set(pk, now);
    state.conversationRepairRunning.add(pk);
    state.syncTelemetry.repairRuns += 1;
    const beforeFp = getConversationFingerprint(pk);

    try {
        const readRelays = getReadRelayUrls();
        const since = Math.floor(Date.now() / 1000) - CONVERSATION_REPAIR_LOOKBACK_SECS;
        const pageLimit = options.deep ? REPAIR_PAGE_LIMIT_DEEP : CONVERSATION_REPAIR_LIMIT;
        const maxPages = options.deep ? REPAIR_MAX_PAGES_DEEP : REPAIR_MAX_PAGES_DEFAULT;
        await ingestPagedGiftWraps(
            readRelays,
            (until) => {
                const f = { kinds: [1059], '#p': [state.publicKey], since };
                if (until !== undefined) {
                    f.until = until;
                }
                return f;
            },
            { pageLimit, maxPages, maxWaitBase: 12000, suppressUi: true }
        );
    } catch (err) {
        console.warn('Conversation repair query failed:', err);
    } finally {
        state.conversationRepairRunning.delete(pk);
    }

    const { updateConversationsList, displayMessages, updateChatHeader } = await import('./ui.js');
    updateConversationsList();
    const afterFp = getConversationFingerprint(pk);
    const changed = beforeFp !== afterFp;
    if (state.currentChat === pk && changed) {
        displayMessages(pk);
        updateChatHeader(pk);
    }
}

export function updateSettingsSyncUiState() {
    const syncBtn = document.getElementById('settingsSyncNowBtn');
    const logBtn = document.getElementById('settingsSyncLogBtn');
    const canUse = Boolean(state.pool && state.publicKey);
    if (syncBtn) {
        syncBtn.disabled = !canUse || state.manualInboxSyncInFlight;
    }
    if (logBtn) {
        logBtn.disabled = !canUse;
    }
}

export async function runManualInboxSyncNow() {
    const statusEl = document.getElementById('settingsSyncStatus');
    const syncBtn = document.getElementById('settingsSyncNowBtn');
    if (!state.pool || !state.publicKey) {
        if (statusEl) statusEl.textContent = 'Connect your extension first.';
        return;
    }
    if (state.manualInboxSyncInFlight) {
        if (statusEl) statusEl.textContent = 'Sync already running…';
        return;
    }
    state.manualInboxSyncInFlight = true;
    state.syncTelemetry.manualSyncRuns += 1;
    try {
        if (syncBtn) syncBtn.disabled = true;
        if (statusEl) statusEl.textContent = 'Reconnecting relays…';
        await connectRelaySet(getReadRelayUrlsUnsorted());
        if (statusEl) statusEl.textContent = 'Fetching full history…';
        await fetchHistoricalGiftWraps({ manual: true });
        if (state.currentChat) {
            if (statusEl) statusEl.textContent = 'Repairing open conversation…';
            await fetchConversationRepair(state.currentChat, { deep: true, force: true });
        }
        if (statusEl) statusEl.textContent = 'Running incremental check…';
        await runIncrementalInboxSync();
        if (statusEl) statusEl.textContent = 'Sync finished.';
        const { updateConversationsList, displayMessages, updateChatHeader } = await import('./ui.js');
        updateConversationsList();
        if (state.currentChat) {
            displayMessages(state.currentChat);
            updateChatHeader(state.currentChat);
        }
    } catch (e) {
        console.error('Manual inbox sync failed:', e);
        if (statusEl) statusEl.textContent = 'Sync failed. Check console and try again.';
    } finally {
        state.manualInboxSyncInFlight = false;
        updateSettingsSyncUiState();
    }
}

// ─── NIP-04 (kind 4) sync ─────────────────────────────────────────────────────

export function stopIncrementalNip04Sync() {
    if (state.incrementalNip04TimerId) {
        clearInterval(state.incrementalNip04TimerId);
        state.incrementalNip04TimerId = null;
    }
}

export function startIncrementalNip04Sync() {
    stopIncrementalNip04Sync();
    state.incrementalNip04TimerId = setInterval(() => {
        void runIncrementalNip04Sync();
    }, NIP04_INCREMENTAL_INTERVAL_MS);
}

export async function runIncrementalNip04Sync() {
    if (!state.pool || !state.publicKey) return;
    if (typeof window.nostr?.nip04?.decrypt !== 'function') return;
    try {
        const nowSec = Math.floor(Date.now() / 1000);
        const baseline = state.lastKind4ProcessedSec > 0 ? state.lastKind4ProcessedSec : nowSec - 24 * 60 * 60;
        const since = Math.max(0, baseline - 2 * 60 * 60);
        const { handleKind4Event } = await import('./messages.js');
        const relays = getReadRelayUrls();
        const [received, sent] = await Promise.all([
            state.pool.querySync(relays, { kinds: [4], '#p': [state.publicKey], since }, { maxWait: 10000 }).catch(() => []),
            state.pool.querySync(relays, { kinds: [4], authors: [state.publicKey], since }, { maxWait: 10000 }).catch(() => []),
        ]);
        const seen = new Set();
        const events = [...received, ...sent].filter((ev) => { if (seen.has(ev.id)) return false; seen.add(ev.id); return true; });
        events.sort((a, b) => a.created_at - b.created_at);
        for (const ev of events) {
            await handleKind4Event(ev);
        }
        const maxTs = events.reduce((m, ev) => Math.max(m, ev.created_at), state.lastKind4ProcessedSec);
        if (maxTs > state.lastKind4ProcessedSec) {
            state.lastKind4ProcessedSec = maxTs;
            dbSaveNip04Cursor(maxTs);
        }
        const { updateConversationsList } = await import('./ui.js');
        updateConversationsList();
    } catch (err) {
        console.warn('Incremental NIP-04 sync failed:', err);
    }
}

export async function loadHistoricalNip04Messages() {
    if (!state.pool || !state.publicKey) return;
    if (typeof window.nostr?.nip04?.decrypt !== 'function') {
        console.info('NIP-04: window.nostr.nip04 not available, skipping history load');
        return;
    }
    try {
        const nowSec = Math.floor(Date.now() / 1000);
        const since = nowSec - NIP04_HISTORY_LOOKBACK_SECS;
        const { handleKind4Event } = await import('./messages.js');
        const relays = getReadRelayUrls();
        const PAGE_LIMIT = 500;
        const MAX_PAGES = 6;
        const allSeen = new Set();
        const allEvents = [];

        // Page through received and sent in parallel per page
        for (let page = 0; page < MAX_PAGES; page++) {
            const until = allEvents.length > 0
                ? allEvents[allEvents.length - 1].created_at - 1
                : undefined;
            const filter = (extra) => ({ kinds: [4], since, limit: PAGE_LIMIT, ...extra, ...(until !== undefined ? { until } : {}) });
            const [received, sent] = await Promise.all([
                state.pool.querySync(relays, filter({ '#p': [state.publicKey] }), { maxWait: 20000 }).catch(() => []),
                state.pool.querySync(relays, filter({ authors: [state.publicKey] }), { maxWait: 20000 }).catch(() => []),
            ]);
            const pageEvents = [...received, ...sent].filter((ev) => {
                if (allSeen.has(ev.id)) return false;
                allSeen.add(ev.id);
                return true;
            });
            if (pageEvents.length === 0) break;
            pageEvents.sort((a, b) => b.created_at - a.created_at);
            allEvents.push(...pageEvents);
            if (received.length < PAGE_LIMIT && sent.length < PAGE_LIMIT) break;
        }

        allEvents.sort((a, b) => a.created_at - b.created_at);
        for (const ev of allEvents) {
            await handleKind4Event(ev);
        }
        const maxTs = allEvents.reduce((m, ev) => Math.max(m, ev.created_at), state.lastKind4ProcessedSec);
        if (maxTs > state.lastKind4ProcessedSec) {
            state.lastKind4ProcessedSec = maxTs;
            dbSaveNip04Cursor(maxTs);
        }
        const { updateConversationsList } = await import('./ui.js');
        updateConversationsList();
    } catch (err) {
        console.warn('NIP-04 history load failed:', err);
    }
}

export function scheduleMobileCatchup(reason = 'unknown') {
    if (!state.pool || !state.publicKey) return;
    if (state.mobileCatchupTimer) {
        clearTimeout(state.mobileCatchupTimer);
    }
    state.mobileCatchupTimer = setTimeout(() => {
        state.mobileCatchupTimer = null;
        console.log('Running mobile catch-up:', reason);
        try {
            if (state.messageSubscription) {
                state.messageSubscription.close();
            }
        } catch (e) {
            console.warn('Closing message subscription during catch-up failed:', e);
        }
        state.messageSubscription = null;
        import('./messages.js').then(({ subscribeToMessages }) => {
            subscribeToMessages();
        });
        // Use incremental sync (cursor-based) rather than a full historical re-fetch
        // so mobile foreground events don't re-decrypt thousands of already-seen wraps.
        void runIncrementalInboxSync();
    }, 350);
}
