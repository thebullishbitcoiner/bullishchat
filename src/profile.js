import { state } from './state.js';
import { normalizePubkey, NOSTR_ARCHIVES_PROFILES_METADATA_URL, PROFILE_METADATA_BATCH_SIZE } from './constants.js';
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
                state.userProfiles[pk] = {
                    ...(state.userProfiles[pk] || emptyUserProfile()),
                    ...profile
                };
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
 * Returns the resolved profile, or null on a transient failure (query itself errored).
 * A relay query that completes but finds no usable kind-0 is a confirmed absence and is
 * cached as empty; a query that throws is not — that distinction matters because caching
 * emptyUserProfile() on every failure used to lock a pubkey to "unknown" for the whole
 * session even after a one-off network blip.
 */
export async function fetchUserProfileFromRelays(pubkey) {
    let events;
    try {
        events = await state.pool.querySync(
            getReadRelayUrlsUnsorted(),
            { kinds: [0], authors: [pubkey], limit: 5 },
            { maxWait: 6000, onauth: nostrAuthHandler }
        );
    } catch (error) {
        console.error('Relay profile fetch failed for', pubkey, error);
        return null;
    }

    for (const event of (events || []).sort((a, b) => (b.created_at || 0) - (a.created_at || 0))) {
        try {
            const profile = normalizeProfileMetadata(JSON.parse(event.content));
            state.userProfiles[pubkey] = profile;
            dbSaveProfile(pubkey, profile);
            return profile;
        } catch (parseError) {
            console.warn('Skipping malformed kind-0 event for', pubkey, parseError);
        }
    }

    // Relays answered but had no usable kind-0 — confirmed absence, safe to cache.
    if (!state.userProfiles[pubkey]) state.userProfiles[pubkey] = emptyUserProfile();
    return state.userProfiles[pubkey];
}

// Fetch user profile with hybrid strategy: API first, relay fallback.
export async function fetchUserProfile(pubkey) {
    const pk = normalizePubkey(pubkey);
    if (state.userProfiles[pk]) {
        return state.userProfiles[pk]; // Already cached
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
                state.userProfiles[pk] = profile;
                dbSaveProfile(pk, profile);
                state.profileFetchFailedAt.delete(pk);
                return profile;
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

/** After bulk inbox load, fetch display names without blocking decrypt. */
export function prefetchMissingConversationProfiles() {
    const missingPubkeys = Object.keys(state.conversations).filter((pubkey) => !state.userProfiles[pubkey]);
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
                        state.userProfiles[pubkey] = profile;
                        dbSaveProfile(pubkey, profile);
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
