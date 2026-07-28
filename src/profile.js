import { state } from './state.js';
import {
    normalizePubkey,
    NOSTR_ARCHIVES_PROFILES_METADATA_URL,
    PROFILE_METADATA_BATCH_SIZE,
    PROFILE_CACHE_TTL_MS
} from './constants.js';
import { dbSaveProfile } from './db.js';
import { getReadRelayUrlsUnsorted, nostrAuthHandler } from './relay.js';

export function emptyUserProfile() {
    return { name: null, display_name: null, picture: null, about: null, nip05: null };
}

export function normalizeProfileMetadata(profile = {}) {
    return {
        name: profile.name || profile.display_name || null,
        display_name: profile.display_name || profile.name || null,
        picture: profile.picture || null,
        about: profile.about || null,
        nip05: profile.nip05 || null
    };
}

/** Tag a profile with when it was fetched, so staleness can be judged after a reload
 *  (the IndexedDB cache is restored into state.userProfiles before any network call). */
function stampProfile(profile) {
    return { ...profile, fetchedAt: Date.now() };
}

function isProfileStale(profile) {
    return !profile?.fetchedAt || Date.now() - profile.fetchedAt >= PROFILE_CACHE_TTL_MS;
}

function profilesEqual(a, b) {
    if (!a || !b) return a === b;
    return (
        a.name === b.name &&
        a.display_name === b.display_name &&
        a.picture === b.picture &&
        a.about === b.about &&
        a.nip05 === b.nip05
    );
}

export async function fetchProfilesMetadataBatch(pubkeys) {
    const keys = [...new Set(pubkeys.map((pk) => normalizePubkey(pk)).filter(Boolean))];
    if (!keys.length) {
        return new Map();
    }
    const res = await fetch(NOSTR_ARCHIVES_PROFILES_METADATA_URL, {
        method: 'POST',
        headers: {
            Accept: 'application/json',
            'Content-Type': 'application/json'
        },
        body: JSON.stringify({ pubkeys: keys })
    });
    if (!res.ok) {
        throw new Error(`Profile metadata failed (${res.status})`);
    }
    const json = await res.json();
    const out = new Map();
    const profiles = Array.isArray(json?.profiles) ? json.profiles : [];
    for (const profile of profiles) {
        if (!profile?.pubkey) continue;
        const pk = normalizePubkey(profile.pubkey);
        out.set(pk, normalizeProfileMetadata(profile));
    }
    return out;
}

/** Load kind-0 style metadata from Nostr Archives for emoji-set authors not already in cache. */
export async function enrichDiscoverEmojiSetAuthors(pubkeys) {
    const keys = [
        ...new Set(
            (pubkeys || [])
                .map((pk) => (typeof pk === 'string' && /^[a-fA-F0-9]{64}$/.test(pk) ? normalizePubkey(pk) : ''))
                .filter(Boolean)
        )
    ];
    const missing = keys.filter((pk) => {
        const p = state.userProfiles[pk];
        return !p || (!p.display_name && !p.name);
    });
    if (!missing.length) {
        return;
    }
    try {
        for (let i = 0; i < missing.length; i += PROFILE_METADATA_BATCH_SIZE) {
            const slice = missing.slice(i, i + PROFILE_METADATA_BATCH_SIZE);
            const map = await fetchProfilesMetadataBatch(slice);
            for (const [pk, profile] of map) {
                if (!profile || (!profile.display_name && !profile.name)) {
                    continue;
                }
                state.userProfiles[pk] = stampProfile({
                    ...(state.userProfiles[pk] || emptyUserProfile()),
                    ...profile
                });
            }
        }
    } catch (e) {
        console.warn('[emoji-discovery] Nostr Archives author metadata failed:', e);
    }
}

/** Cooldown after a transient (network/timeout) failure before we retry the same pubkey,
 *  so a flaky connection doesn't turn into constant refetching but also never gets stuck. */
const PROFILE_RETRY_COOLDOWN_MS = 30_000;

/**
 * Queries relays for a pubkey's newest usable kind-0. `ok: false` means the query itself
 * errored (transient — caller should not treat this as "no profile"); `ok: true` with
 * `profile: null` means relays answered but had nothing usable (confirmed absence).
 */
async function queryRelayProfile(pubkey) {
    let events;
    try {
        events = await state.pool.querySync(
            getReadRelayUrlsUnsorted(),
            { kinds: [0], authors: [pubkey], limit: 5 },
            { maxWait: 6000, onauth: nostrAuthHandler }
        );
    } catch (error) {
        console.error('Relay profile fetch failed for', pubkey, error);
        return { ok: false, profile: null };
    }

    for (const event of (events || []).sort((a, b) => (b.created_at || 0) - (a.created_at || 0))) {
        try {
            return { ok: true, profile: normalizeProfileMetadata(JSON.parse(event.content)) };
        } catch (parseError) {
            console.warn('Skipping malformed kind-0 event for', pubkey, parseError);
        }
    }
    return { ok: true, profile: null };
}

/**
 * Returns the resolved profile, or null on a transient failure (query itself errored).
 * A relay query that completes but finds no usable kind-0 is a confirmed absence and is
 * cached as empty; a query that throws is not — that distinction matters because caching
 * emptyUserProfile() on every failure used to lock a pubkey to "unknown" for the whole
 * session even after a one-off network blip.
 */
export async function fetchUserProfileFromRelays(pubkey) {
    const { ok, profile } = await queryRelayProfile(pubkey);
    if (profile) {
        const stamped = stampProfile(profile);
        state.userProfiles[pubkey] = stamped;
        dbSaveProfile(pubkey, stamped);
        return stamped;
    }
    if (!ok) return null;

    // Relays answered but had no usable kind-0 — confirmed absence, safe to cache.
    if (!state.userProfiles[pubkey]) state.userProfiles[pubkey] = stampProfile(emptyUserProfile());
    return state.userProfiles[pubkey];
}

/**
 * Stale-while-revalidate: re-checks a cached profile that's past its TTL without blocking
 * whoever is currently reading the cache. If the fetch fails or turns up nothing, the last
 * known-good profile is left alone (a blip on one relay round shouldn't erase a known name/avatar) —
 * it's just gated by the same retry cooldown as a hard failure so we don't recheck every render.
 */
function refreshProfileInBackground(pk, previous) {
    if (state.profileFetchInFlight.has(pk)) return;
    const failedAt = state.profileFetchFailedAt.get(pk);
    if (failedAt && Date.now() - failedAt < PROFILE_RETRY_COOLDOWN_MS) return;

    const pending = (async () => {
        let profile = null;
        try {
            const map = await fetchProfilesMetadataBatch([pk]);
            profile = map.get(pk) || null;
        } catch (error) {
            console.warn('Background profile refresh (API) failed for', pk, error);
        }
        if (!profile) {
            profile = (await queryRelayProfile(pk)).profile;
        }
        if (!profile) {
            state.profileFetchFailedAt.set(pk, Date.now());
            return;
        }

        const stamped = stampProfile(profile);
        const changed = !profilesEqual(previous, stamped);
        state.userProfiles[pk] = stamped;
        dbSaveProfile(pk, stamped);
        state.profileFetchFailedAt.delete(pk);
        if (changed) {
            const { queueConversationsListUpdate, queueChatHeaderUpdate } = await import('./queue.js');
            queueConversationsListUpdate();
            queueChatHeaderUpdate(pk);
        }
    })();
    state.profileFetchInFlight.set(pk, pending);
    void pending.finally(() => state.profileFetchInFlight.delete(pk));
}

// Fetch user profile with hybrid strategy: API first, relay fallback.
export async function fetchUserProfile(pubkey) {
    const pk = normalizePubkey(pubkey);
    const cached = state.userProfiles[pk];
    if (cached) {
        if (isProfileStale(cached)) {
            refreshProfileInBackground(pk, cached);
        }
        return cached; // Already cached — return instantly, refresh (if due) happens in the background
    }
    if (state.profileFetchInFlight.has(pk)) {
        return state.profileFetchInFlight.get(pk);
    }
    const failedAt = state.profileFetchFailedAt.get(pk);
    if (failedAt && Date.now() - failedAt < PROFILE_RETRY_COOLDOWN_MS) {
        return emptyUserProfile(); // still cooling down; don't hammer, don't cache
    }

    const pending = (async () => {
        try {
            const map = await fetchProfilesMetadataBatch([pk]);
            const profile = map.get(pk);
            if (profile) {
                const stamped = stampProfile(profile);
                state.userProfiles[pk] = stamped;
                dbSaveProfile(pk, stamped);
                state.profileFetchFailedAt.delete(pk);
                return stamped;
            }
        } catch (error) {
            console.warn('Nostr Archives metadata fetch failed for', pk, error);
        }

        const relayProfile = await fetchUserProfileFromRelays(pk);
        if (relayProfile) {
            state.profileFetchFailedAt.delete(pk);
            return relayProfile;
        }

        // Both the API and the relay query failed outright (network/timeout), rather than
        // confirming the profile doesn't exist. Don't cache permanently — just cool down.
        state.profileFetchFailedAt.set(pk, Date.now());
        return emptyUserProfile();
    })();
    state.profileFetchInFlight.set(pk, pending);
    try {
        return await pending;
    } finally {
        state.profileFetchInFlight.delete(pk);
    }
}

// Get display name for a pubkey (with fallback to short pubkey)
export function getDisplayName(pubkey) {
    if (typeof pubkey !== 'string' || !pubkey) {
        return '';
    }
    const pk = /^[a-fA-F0-9]{64}$/.test(pubkey) ? normalizePubkey(pubkey) : pubkey;
    const profile = state.userProfiles[pk];
    if (profile && (profile.display_name || profile.name)) {
        return profile.display_name || profile.name;
    }
    // Fallback to short pubkey
    return pk.slice(0, 8) + '...' + pk.slice(-8);
}

/** After bulk inbox load, fetch display names without blocking decrypt. Also runs on the
 *  incremental inbox sync timer, which doubles as the periodic check for stale cached
 *  profiles — fetchUserProfile() is a no-op for fresh ones and background-refreshes stale ones. */
export function prefetchMissingConversationProfiles() {
    const pubkeys = Object.keys(state.conversations);
    const missingPubkeys = pubkeys.filter((pubkey) => !state.userProfiles[pubkey]);

    for (const pubkey of pubkeys) {
        const cached = state.userProfiles[pubkey];
        if (cached && isProfileStale(cached)) {
            void fetchUserProfile(pubkey);
        }
    }

    if (!missingPubkeys.length) {
        return;
    }

    const chunks = [];
    for (let i = 0; i < missingPubkeys.length; i += PROFILE_METADATA_BATCH_SIZE) {
        chunks.push(missingPubkeys.slice(i, i + PROFILE_METADATA_BATCH_SIZE));
    }

    for (const chunk of chunks) {
        void (async () => {
            const unresolved = [];
            try {
                const map = await fetchProfilesMetadataBatch(chunk);
                for (const pubkey of chunk) {
                    const profile = map.get(normalizePubkey(pubkey));
                    if (profile) {
                        const stamped = stampProfile(profile);
                        state.userProfiles[pubkey] = stamped;
                        dbSaveProfile(pubkey, stamped);
                    } else {
                        unresolved.push(pubkey);
                    }
                }
            } catch (error) {
                console.warn('Batch profile metadata prefetch failed; falling back to relays.', error);
                unresolved.push(...chunk);
            }

            if (unresolved.length) {
                await Promise.allSettled(unresolved.map((pubkey) => fetchUserProfile(pubkey)));
            }

            // Import queue functions lazily to avoid circular dependency issues at module load time
            const { queueConversationsListUpdate, queueChatHeaderUpdate } = await import('./queue.js');
            queueConversationsListUpdate();
            for (const pubkey of chunk) {
                queueChatHeaderUpdate(pubkey);
            }
        })();
    }
}
