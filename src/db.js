import { state } from './state.js';
import { IDB_NAME, IDB_VERSION } from './constants.js';

export async function initDB() {
    try {
        state.db = await new Promise((resolve, reject) => {
            const req = indexedDB.open(IDB_NAME, IDB_VERSION);
            req.onupgradeneeded = (e) => {
                const d = e.target.result;
                if (!d.objectStoreNames.contains('messages')) {
                    const ms = d.createObjectStore('messages', { keyPath: 'id' });
                    ms.createIndex('by-conv', 'conversationPubkey');
                }
                if (!d.objectStoreNames.contains('profiles')) {
                    d.createObjectStore('profiles', { keyPath: 'pubkey' });
                }
                if (!d.objectStoreNames.contains('seenWraps')) {
                    d.createObjectStore('seenWraps', { keyPath: 'id' });
                }
                if (!d.objectStoreNames.contains('meta')) {
                    d.createObjectStore('meta', { keyPath: 'key' });
                }
                if (!d.objectStoreNames.contains('nip04Messages')) {
                    const n4 = d.createObjectStore('nip04Messages', { keyPath: 'id' });
                    n4.createIndex('by-conv', 'conversationPubkey');
                }
                if (!d.objectStoreNames.contains('seenKind4')) {
                    d.createObjectStore('seenKind4', { keyPath: 'id' });
                }
            };
            req.onsuccess = (e) => resolve(e.target.result);
            req.onerror = (e) => reject(e.target.error);
        });
    } catch (e) {
        console.warn('IndexedDB unavailable, running in-memory only:', e);
        state.db = null;
    }
}

export function idbGet(store, key) {
    if (!state.db) return Promise.resolve(undefined);
    return new Promise((resolve, reject) => {
        const tx = state.db.transaction(store, 'readonly');
        const req = tx.objectStore(store).get(key);
        req.onsuccess = () => resolve(req.result);
        req.onerror = () => reject(req.error);
    });
}

export function idbPut(store, value) {
    if (!state.db) return Promise.resolve();
    return new Promise((resolve, reject) => {
        const tx = state.db.transaction(store, 'readwrite');
        const req = tx.objectStore(store).put(value);
        req.onsuccess = () => resolve();
        req.onerror = () => reject(req.error);
    });
}

/** Deletes every row in `store` matching `conversationPubkey` via the existing by-conv index. */
export function idbDeleteConversationMessages(store, conversationPubkey) {
    if (!state.db) return Promise.resolve();
    return new Promise((resolve) => {
        const tx = state.db.transaction(store, 'readwrite');
        const req = tx.objectStore(store).index('by-conv').openCursor(IDBKeyRange.only(conversationPubkey));
        req.onsuccess = (e) => {
            const cursor = e.target.result;
            if (cursor) {
                cursor.delete();
                cursor.continue();
            }
        };
        tx.oncomplete = resolve;
        tx.onerror = resolve;
    });
}

export function idbGetAll(store) {
    if (!state.db) return Promise.resolve([]);
    return new Promise((resolve, reject) => {
        const tx = state.db.transaction(store, 'readonly');
        const req = tx.objectStore(store).getAll();
        req.onsuccess = () => resolve(req.result || []);
        req.onerror = () => reject(req.error);
    });
}

export function idbClearAll() {
    if (!state.db) return Promise.resolve();
    return new Promise((resolve) => {
        const stores = ['messages', 'profiles', 'seenWraps', 'meta', 'nip04Messages', 'seenKind4'];
        const tx = state.db.transaction(stores, 'readwrite');
        for (const s of stores) tx.objectStore(s).clear();
        tx.oncomplete = resolve;
        tx.onerror = resolve;
    });
}

export async function loadStateFromDB(ownerPubkey) {
    if (!state.db) return;
    try {
        const stored = await idbGet('meta', 'ownerPubkey');
        if (stored && stored.value !== ownerPubkey) {
            console.info('DB: different pubkey detected — clearing stored state.');
            await idbClearAll();
        }
        await idbPut('meta', { key: 'ownerPubkey', value: ownerPubkey });

        const [wrapRows, msgRows, profileRows, cursorRow, dmRelayRow, blossomRow, mutedRow] = await Promise.all([
            idbGetAll('seenWraps'),
            idbGetAll('messages'),
            idbGetAll('profiles'),
            idbGet('meta', 'lastInboxGiftWrapProcessedSec'),
            idbGet('meta', 'dmRelayUrls'),
            idbGet('meta', 'blossomServers'),
            idbGet('meta', 'mutedPubkeys'),
        ]);

        for (const { id } of wrapRows) {
            state.seenGiftWrapEventIds.add(id);
        }

        for (const msg of msgRows) {
            const { conversationPubkey: pk, ...msgData } = msg;
            if (!pk) continue;
            if (!state.conversations[pk]) state.conversations[pk] = [];
            state.conversations[pk].push(msgData);
            if (msg.id) state.seenRumorIds.add(msg.id);
        }
        for (const pk of Object.keys(state.conversations)) {
            state.conversations[pk].sort((a, b) => a.timestamp - b.timestamp);
        }

        for (const p of profileRows) {
            const { pubkey, ...fields } = p;
            state.userProfiles[pubkey] = fields;
        }

        if (cursorRow?.value > 0) {
            state.lastInboxGiftWrapProcessedSec = cursorRow.value;
        }

        // Restore previously-discovered inbox relay list so kind 10050 re-discovery
        // can bootstrap from the user's own relay rather than only the app defaults.
        if (Array.isArray(dmRelayRow?.value) && dmRelayRow.value.length > 0) {
            state.dmRelayUrls = dmRelayRow.value;
        }

        if (Array.isArray(blossomRow?.value) && blossomRow.value.length > 0) {
            state.blossomServers = blossomRow.value;
        }

        if (Array.isArray(mutedRow?.value) && mutedRow.value.length > 0) {
            state.mutedPubkeys = new Set(mutedRow.value);
        }

        console.info(
            `DB: loaded ${msgRows.length} messages, ${wrapRows.length} seen wraps, ${profileRows.length} profiles; cursor=${state.lastInboxGiftWrapProcessedSec}; dmRelays=${state.dmRelayUrls.join(',')}`
        );
    } catch (e) {
        console.warn('Failed to load state from IndexedDB:', e);
    }
}

export function dbSaveMessage(conversationPubkey, message) {
    if (!state.db || !message?.id) return;
    void idbPut('messages', { ...message, conversationPubkey }).catch((e) =>
        console.warn('DB: save message failed:', e)
    );
}

export function dbSaveProfile(pubkey, profile) {
    if (!state.db || !pubkey || !profile) return;
    void idbPut('profiles', { pubkey, ...profile }).catch((e) =>
        console.warn('DB: save profile failed:', e)
    );
}

export function dbMarkWrapSeen(id) {
    if (!state.db || !id) return;
    void idbPut('seenWraps', { id }).catch((e) => console.warn('DB: mark wrap failed:', e));
}

export function dbSaveLastTimestamp(ts) {
    if (!state.db || !(ts > 0)) return;
    void idbPut('meta', { key: 'lastInboxGiftWrapProcessedSec', value: ts }).catch((e) =>
        console.warn('DB: save cursor failed:', e)
    );
}

export function dbSaveNip04Message(conversationPubkey, message) {
    if (!state.db || !message?.id) return;
    void idbPut('nip04Messages', { ...message, conversationPubkey }).catch((e) =>
        console.warn('DB: save nip04 message failed:', e)
    );
}

export function dbMarkKind4Seen(id) {
    if (!state.db || !id) return;
    void idbPut('seenKind4', { id }).catch((e) => console.warn('DB: mark kind4 failed:', e));
}

export function dbSaveNip04Cursor(ts) {
    if (!state.db || !(ts > 0)) return;
    void idbPut('meta', { key: 'lastKind4ProcessedSec', value: ts }).catch((e) =>
        console.warn('DB: save nip04 cursor failed:', e)
    );
}

export async function loadNip04StateFromDB() {
    if (!state.db) return;
    try {
        const [seenRows, msgRows, cursorRow] = await Promise.all([
            idbGetAll('seenKind4'),
            idbGetAll('nip04Messages'),
            idbGet('meta', 'lastKind4ProcessedSec'),
        ]);

        for (const { id } of seenRows) {
            state.seenKind4EventIds.add(id);
        }

        for (const msg of msgRows) {
            const { conversationPubkey: pk, ...msgData } = msg;
            if (!pk) continue;
            if (!state.nip04Conversations[pk]) state.nip04Conversations[pk] = [];
            state.nip04Conversations[pk].push(msgData);
        }
        for (const pk of Object.keys(state.nip04Conversations)) {
            state.nip04Conversations[pk].sort((a, b) => a.timestamp - b.timestamp);
        }

        if (cursorRow?.value > 0) {
            state.lastKind4ProcessedSec = cursorRow.value;
        }

        console.info(
            `DB: loaded ${msgRows.length} nip04 messages, ${seenRows.length} seen kind4; cursor=${state.lastKind4ProcessedSec}`
        );
    } catch (e) {
        console.warn('Failed to load NIP-04 state from IndexedDB:', e);
    }
}
