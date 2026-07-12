import { generateSecretKey, getPublicKey, getEventHash, finalizeEvent } from 'nostr-tools';
import { encrypt as nip44Encrypt, getConversationKey } from 'nostr-tools/nip44';
import { decodeInvoice } from '@getalby/lightning-tools/bolt11';

import { state } from './state.js';
import {
    normalizePubkey,
    LIGHTNING_INVOICE_RE,
    HTTP_URL_IN_TEXT_RE,
    RELAY_URLS,
    MAX_IMAGE_UPLOAD_BYTES
} from './constants.js';
import { uploadImageToNostr } from './blossom.js';
import { dbMarkWrapSeen, dbSaveMessage, dbSaveNip04Message, dbMarkKind4Seen } from './db.js';
import { getReadRelayUrls, getReadRelayUrlsUnsorted, resolveInboxRelays, getRandomPastTimestamp, nostrAuthHandler } from './relay.js';
import { fetchUserProfile } from './profile.js';
import { queueActiveChatRender, queueConversationsListUpdate, queueChatHeaderUpdate } from './queue.js';

export function normalizeReactionContent(content) {
    if (typeof content !== 'string') return null;
    const c = content.trim();
    if (!c) return null;
    if (c === '+') return '👍';
    if (c === '-') return '👎';
    return c.slice(0, 16);
}

export function parseBolt11InvoiceFromText(content) {
    if (typeof content !== 'string') return null;
    const match = content.match(LIGHTNING_INVOICE_RE);
    if (!match) return null;
    const invoice = (match[2] || '').toLowerCase();
    if (!invoice) return null;
    const decoded = decodeInvoice(invoice);
    if (!decoded) return null;

    const cleanedText = (content.replace(match[0], ' ').replace(/\s+/g, ' ').trim());
    return {
        invoice,
        cleanedText,
        decoded
    };
}

export function revokeActiveMessageBlobs() {
    for (const u of state.activeMessageBlobUrls) {
        try {
            URL.revokeObjectURL(u);
        } catch {
            /* ignore */
        }
    }
    state.activeMessageBlobUrls.clear();
}

export function trimUrlTrailingPunctuation(url) {
    let u = url;
    while (u.length && /[.,;:!?)\]}>'"”’]$/.test(u)) {
        u = u.slice(0, -1);
    }
    return u;
}

export function looksLikeDirectImageUrl(url) {
    return /\.(png|jpe?g|gif|webp|avif|svg)(\?|#|$)/i.test(url);
}

export function isSafeHttpUrl(url) {
    try {
        const u = new URL(url);
        return u.protocol === 'http:' || u.protocol === 'https:';
    } catch {
        return false;
    }
}

export function hexToBytes(hex) {
    const s = String(hex || '')
        .replace(/^0x/i, '')
        .replace(/\s/g, '');
    if (!s.length || s.length % 2 !== 0 || !/^[0-9a-fA-F]+$/.test(s)) {
        return null;
    }
    const out = new Uint8Array(s.length / 2);
    for (let i = 0; i < out.length; i++) {
        out[i] = parseInt(s.slice(i * 2, i * 2 + 2), 16);
    }
    return out;
}

export async function sha256HexOfBuffer(buf) {
    const digest = await crypto.subtle.digest('SHA-256', buf);
    return [...new Uint8Array(digest)].map((b) => b.toString(16).padStart(2, '0')).join('');
}

export async function decryptAesGcmRaw(keyBytes, ivBytes, cipherWithTag) {
    const cryptoKey = await crypto.subtle.importKey('raw', keyBytes, { name: 'AES-GCM' }, false, ['decrypt']);
    return new Uint8Array(
        await crypto.subtle.decrypt({ name: 'AES-GCM', iv: ivBytes }, cryptoKey, cipherWithTag)
    );
}

/**
 * Try NIP-17 kind-15 AES-GCM: ciphertext at URL, `x` = SHA-256 of ciphertext.
 * @returns {Promise<string|null>} object URL for decrypted bytes
 */
export async function tryDecryptKind15ToBlobUrl(meta) {
    if (!meta?.url || !isSafeHttpUrl(meta.url) || meta.encryptionAlgorithm !== 'aes-gcm') return null;
    const keyBytes = hexToBytes(meta.decryptionKey);
    const nonceBytes = hexToBytes(meta.decryptionNonce);
    if (!keyBytes || !nonceBytes) return null;
    if (![16, 24, 32].includes(keyBytes.length)) return null;
    if (![12, 16].includes(nonceBytes.length)) return null;

    let res;
    try {
        res = await fetch(meta.url, { mode: 'cors', credentials: 'omit' });
    } catch {
        return null;
    }
    if (!res.ok) return null;
    const buf = await res.arrayBuffer();
    const ct = new Uint8Array(buf);

    if (meta.xHash) {
        const expected = meta.xHash.replace(/^0x/i, '').toLowerCase();
        try {
            const h = await sha256HexOfBuffer(ct);
            if (h !== expected) return null;
        } catch {
            return null;
        }
    }

    let plain;
    try {
        plain = await decryptAesGcmRaw(keyBytes, nonceBytes, ct);
    } catch {
        return null;
    }

    const mime =
        typeof meta.fileType === 'string' && meta.fileType.startsWith('image/')
            ? meta.fileType
            : 'application/octet-stream';
    const blob = new Blob([plain], { type: mime });
    const blobUrl = URL.createObjectURL(blob);
    state.activeMessageBlobUrls.add(blobUrl);
    return blobUrl;
}

/**
 * Append text with http(s) links and inline images (safe DOM only).
 * @param {HTMLElement} parent
 * @param {string} text
 * @param {{ bare?: boolean }} [opts] — bare: omit .message-text (e.g. nested in file card)
 */
export function appendRichMessageContent(parent, text, opts = {}) {
    if (text == null || text === '') return;
    const inner = document.createElement('div');
    inner.className = opts.bare ? 'message-text-rich' : 'message-text message-text-rich';
    fillRichTextInto(inner, String(text));
    parent.appendChild(inner);
}

export function fillRichTextInto(el, text) {
    el.textContent = '';
    if (!text) return;

    const re = new RegExp(HTTP_URL_IN_TEXT_RE.source, HTTP_URL_IN_TEXT_RE.flags);
    let last = 0;
    let m;
    let any = false;
    while ((m = re.exec(text)) !== null) {
        any = true;
        if (m.index > last) {
            el.appendChild(document.createTextNode(text.slice(last, m.index)));
        }
        const raw = m[0];
        const url = trimUrlTrailingPunctuation(raw);
        last = m.index + raw.length;

        if (!isSafeHttpUrl(url)) {
            el.appendChild(document.createTextNode(raw));
            continue;
        }

        if (looksLikeDirectImageUrl(url)) {
            const wrap = document.createElement('div');
            wrap.className = 'message-inline-image-wrap';
            const link = document.createElement('a');
            link.href = url;
            link.target = '_blank';
            link.rel = 'noopener noreferrer';
            link.className = 'message-inline-image-link';
            const img = document.createElement('img');
            img.className = 'message-inline-image';
            img.alt = '';
            img.loading = 'lazy';
            img.decoding = 'async';
            img.referrerPolicy = 'no-referrer';
            img.src = url;
            img.addEventListener(
                'error',
                () => {
                    wrap.replaceChildren();
                    const a = document.createElement('a');
                    a.href = url;
                    a.target = '_blank';
                    a.rel = 'noopener noreferrer';
                    a.className = 'message-link';
                    a.textContent = url;
                    wrap.appendChild(a);
                },
                { once: true }
            );
            link.appendChild(img);
            wrap.appendChild(link);
            el.appendChild(wrap);
        } else {
            const a = document.createElement('a');
            a.href = url;
            a.target = '_blank';
            a.rel = 'noopener noreferrer';
            a.className = 'message-link';
            a.textContent = url;
            el.appendChild(a);
        }
    }
    if (!any) {
        el.textContent = text;
        return;
    }
    if (last < text.length) {
        el.appendChild(document.createTextNode(text.slice(last)));
    }
}

export function appendInlineImageFromBlobUrl(parent, blobUrl) {
    const wrap = document.createElement('div');
    wrap.className = 'message-inline-image-wrap';
    const img = document.createElement('img');
    img.className = 'message-inline-image';
    img.alt = '';
    img.decoding = 'async';
    img.src = blobUrl;
    wrap.appendChild(img);
    parent.appendChild(wrap);
}

/**
 * Kind 15 image: try AES-GCM decrypt, else direct <img> if URL is reachable as image.
 */
export async function loadKind15ImagePreview(previewEl, meta) {
    previewEl.textContent = '';
    if (!meta?.fileType?.startsWith('image/')) {
        previewEl.hidden = true;
        return;
    }
    previewEl.hidden = false;

    const loading = document.createElement('div');
    loading.className = 'file-message-preview-loading';
    loading.textContent = 'Loading…';
    previewEl.appendChild(loading);

    const tryBlob = await tryDecryptKind15ToBlobUrl(meta);
    if (tryBlob) {
        loading.remove();
        appendInlineImageFromBlobUrl(previewEl, tryBlob);
        return;
    }

    if (!meta.encryptionAlgorithm && meta.url && isSafeHttpUrl(meta.url) && looksLikeDirectImageUrl(meta.url)) {
        loading.remove();
        const wrap = document.createElement('div');
        wrap.className = 'message-inline-image-wrap';
        const link = document.createElement('a');
        link.href = meta.url;
        link.target = '_blank';
        link.rel = 'noopener noreferrer';
        link.className = 'message-inline-image-link';
        const img = document.createElement('img');
        img.className = 'message-inline-image';
        img.alt = '';
        img.loading = 'lazy';
        img.referrerPolicy = 'no-referrer';
        img.src = meta.url;
        img.addEventListener(
            'error',
            () => {
                wrap.replaceChildren();
                const err = document.createElement('div');
                err.className = 'file-message-preview-note';
                err.textContent = 'Could not load image (check link or CORS).';
                wrap.appendChild(err);
            },
            { once: true }
        );
        link.appendChild(img);
        wrap.appendChild(link);
        previewEl.appendChild(wrap);
        return;
    }

    if (meta.encryptionAlgorithm === 'aes-gcm' && meta.url) {
        loading.remove();
        const fallbackBubble = document.createElement('div');
        fallbackBubble.className = 'file-message-fallback-bubble';
        appendRichMessageContent(fallbackBubble, meta.url, { bare: true });
        previewEl.appendChild(fallbackBubble);
        return;
    }

    loading.remove();
}

export async function payLightningInvoice(invoice) {
    if (!invoice) {
        throw new Error('Missing invoice');
    }
    const webln = window.webln;
    if (!webln || typeof webln.sendPayment !== 'function') {
        throw new Error('No WebLN wallet found');
    }
    if (typeof webln.enable === 'function') {
        await webln.enable();
    }
    return webln.sendPayment(invoice);
}

export function applyReactionToMessage(message, emoji, fromPubkey) {
    if (!message.reactions) {
        message.reactions = {};
    }
    if (!message.reactions[emoji]) {
        message.reactions[emoji] = { count: 0, reactors: [] };
    }
    const bucket = message.reactions[emoji];
    if (!bucket.reactors.includes(fromPubkey)) {
        bucket.reactors.push(fromPubkey);
        bucket.count += 1;
    }
}

export function applyPendingReactionsForMessage(conversationPubkey, message) {
    if (!message?.id) return;
    const pending = state.pendingReactionsByMessageId.get(message.id);
    if (!pending?.length) return;

    for (const reaction of pending) {
        if (reaction.conversationPubkey !== conversationPubkey) continue;
        applyReactionToMessage(message, reaction.emoji, reaction.fromPubkey);
    }

    const remaining = pending.filter((reaction) => reaction.conversationPubkey !== conversationPubkey);
    if (remaining.length) {
        state.pendingReactionsByMessageId.set(message.id, remaining);
    } else {
        state.pendingReactionsByMessageId.delete(message.id);
        state.pendingReactionFirstSeen.delete(message.id);
    }
}

export function handleReactionRumor(rumor, conversationPubkey, authorPubkey) {
    const kindTag = Array.isArray(rumor.tags)
        ? rumor.tags.find((t) => t[0] === 'k' && typeof t[1] === 'string')
        : null;
    if (kindTag && kindTag[1] !== '14' && kindTag[1] !== '15') {
        return false;
    }

    const eTag = Array.isArray(rumor.tags)
        ? rumor.tags.find((t) => t[0] === 'e' && typeof t[1] === 'string' && t[1].length)
        : null;
    if (!eTag) {
        return false;
    }
    const targetMessageId = eTag[1];
    const emoji = normalizeReactionContent(rumor.content);
    if (!emoji) {
        return false;
    }

    if (!state.conversations[conversationPubkey]) {
        state.conversations[conversationPubkey] = [];
    }

    const targetMessage = state.conversations[conversationPubkey].find((m) => m.id === targetMessageId);
    if (targetMessage) {
        applyReactionToMessage(targetMessage, emoji, authorPubkey);
        dbSaveMessage(conversationPubkey, targetMessage);
    } else {
        const pending = state.pendingReactionsByMessageId.get(targetMessageId) || [];
        pending.push({ conversationPubkey, emoji, fromPubkey: authorPubkey });
        state.pendingReactionsByMessageId.set(targetMessageId, pending);
        if (!state.pendingReactionFirstSeen.has(targetMessageId)) {
            state.pendingReactionFirstSeen.set(targetMessageId, Date.now());
        }
        // Lazy import to avoid circular dependency with sync.js
        import('./sync.js').then(({ scheduleGapFillForConversation }) => {
            scheduleGapFillForConversation(conversationPubkey);
        });
    }
    return true;
}

export function subscribeToMessages() {
    const readRelays = getReadRelayUrls();
    // `since: now` so this subscription only delivers events that arrive after
    // this moment — historical backfill is handled by fetchHistoricalGiftWraps /
    // runIncrementalInboxSync, avoiding redundant re-decryption of stored events.
    const since = Math.floor(Date.now() / 1000);
    const filter = { kinds: [1059], '#p': [state.publicKey], since };

    state.messageSubscription = state.pool.subscribe(readRelays, filter, {
        onauth: nostrAuthHandler,
        onevent(event) {
            handleGiftWrappedMessage(event).catch((error) => {
                console.error('Error in handleGiftWrappedMessage (non-blocking):', error);
            });
        },
        oneose() {
            console.log('Live subscription EOSE — listening for new messages on', readRelays.length, 'relay(s)');
        }
    });
}

/** @param {{ suppressUi?: boolean }} [options] — suppressUi: batch historical load (single UI refresh at end). */
export async function handleGiftWrappedMessage(giftWrap, options = {}) {
    if (state.seenGiftWrapEventIds.has(giftWrap.id)) {
        return;
    }
    state.seenGiftWrapEventIds.add(giftWrap.id);
    dbMarkWrapSeen(giftWrap.id);

    console.log('Processing gift-wrapped message:', {
        id: giftWrap.id,
        kind: giftWrap.kind,
        pubkey: giftWrap.pubkey,
        tags: giftWrap.tags
    });

    try {
        // Step 1: Unwrap the gift wrap (kind 1059) using NIP-44
        // Gift wrap is encrypted FROM ephemeral key TO our public key
        // We decrypt using our private key via the extension
        if (!window.nostr?.nip44?.decrypt) {
            console.error('Extension does not support nip44.decrypt. Please reconnect with a compatible extension.');
            return;
        }

        console.log('Decrypting gift wrap with ephemeral pubkey:', giftWrap.pubkey);
        let unwrappedJSON;
        try {
            unwrappedJSON = await window.nostr.nip44.decrypt(
                giftWrap.pubkey,
                giftWrap.content
            );
            console.log('Successfully decrypted gift wrap');
        } catch (decryptError) {
            // If decryption fails, this might be a message not intended for us
            // or encrypted with a different key/version. Skip it silently.
            state.syncTelemetry.giftWrapDecryptFail += 1;
            console.warn('Failed to decrypt gift wrap (may not be for us or wrong encryption):', {
                error: decryptError.message,
                eventId: giftWrap.id,
                ephemeralPubkey: giftWrap.pubkey
            });
            return; // Skip this message, continue with others
        }

        const seal = JSON.parse(unwrappedJSON);
        console.log('Unwrapped seal:', { kind: seal.kind, pubkey: seal.pubkey });

        // Step 2: Verify it's a seal (kind 13)
        if (seal.kind !== 13) {
            console.error('Expected kind 13 seal, got:', seal.kind);
            return;
        }

        // Step 3: Decrypt the seal to get the rumor (NIP-17: kind 14 chat, 7 reaction, 15 file, …)
        // NIP-44 peer for decrypt is always the *other* party in the conversation:
        // - Incoming: seal author is the sender → decrypt(seal.pubkey, …).
        // - Our own sender copy: seal author is us; payload was encrypt(recipient, …) → decrypt(recipient, …).
        const sealAuthor = normalizePubkey(seal.pubkey);
        let sealDecryptPeer = seal.pubkey;
        if (sealAuthor === state.publicKey) {
            const sealPTag = Array.isArray(seal.tags)
                ? seal.tags.find((t) => t[0] === 'p' && typeof t[1] === 'string' && t[1].length)
                : null;
            if (!sealPTag) {
                console.warn(
                    'Skipping own kind 13 seal without p tag (cannot determine NIP-44 peer; re-send from updated app to fix).',
                    { eventId: giftWrap.id }
                );
                return;
            }
            sealDecryptPeer = normalizePubkey(sealPTag[1]);
        }

        console.log('Decrypting seal; nip44 peer:', sealDecryptPeer);
        let rumorJSON;
        try {
            rumorJSON = await window.nostr.nip44.decrypt(sealDecryptPeer, seal.content);
            console.log('Successfully decrypted seal');
        } catch (decryptError) {
            // If seal decryption fails, skip this message
            state.syncTelemetry.sealDecryptFail += 1;
            console.warn('Failed to decrypt seal (may not be for us or wrong encryption):', {
                error: decryptError.message,
                eventId: giftWrap.id,
                sealAuthor: seal.pubkey,
                nip44Peer: sealDecryptPeer
            });
            return; // Skip this message, continue with others
        }

        const rumor = JSON.parse(rumorJSON);
        console.log('Unwrapped rumor:', { kind: rumor.kind, pubkey: rumor.pubkey, content: rumor.content?.substring(0, 50) });

        try {
            // Step 4: NIP-17 — kind 14 DMs, kind 7 reactions, kind 15 file messages (see nips/17.md).
            if (rumor.kind !== 14 && rumor.kind !== 7 && rumor.kind !== 15) {
                state.syncTelemetry.rumorUnsupported += 1;
                console.warn('Unsupported rumor kind inside gift wrap (skipping):', rumor.kind);
                return;
            }

            // Step 5: Verify the sender
            if (normalizePubkey(seal.pubkey) !== normalizePubkey(rumor.pubkey)) {
                console.error('Sender pubkey mismatch - potential impersonation attempt');
                return;
            }

            const authorPubkey = normalizePubkey(rumor.pubkey);
            const conversationPubkey = getRumorConversationPubkey(rumor, authorPubkey);
            if (!conversationPubkey) {
                console.error('Outgoing rumor missing p tag; cannot assign conversation');
                return;
            }

            if (!state.conversations[conversationPubkey]) {
                state.conversations[conversationPubkey] = [];
            }

            if (rumor.id) {
                if (state.seenRumorIds.has(rumor.id)) {
                    return;
                }
                state.seenRumorIds.add(rumor.id);
            }

            if (rumor.kind === 7) {
                const applied = handleReactionRumor(rumor, conversationPubkey, authorPubkey);
                if (!applied) {
                    return;
                }
                if (!options.suppressUi) {
                    if (state.currentChat === conversationPubkey) {
                        queueActiveChatRender(conversationPubkey);
                    }
                    // Lazy import to avoid circular dependency
                    const { updateConversationsList } = await import('./ui.js');
                    updateConversationsList();
                }
                return;
            }

            // Same logical message can appear locally first, then again from our self-addressed gift wrap
            if (rumor.id && state.conversations[conversationPubkey].some((m) => m.id === rumor.id)) {
                return;
            }

            let newMsg;
            if (rumor.kind === 15) {
                const fileMeta = parseKind15FileMeta(rumor);
                if (!fileMeta) {
                    console.warn('Kind 15 rumor missing file URL; skipping', { id: rumor.id });
                    return;
                }
                newMsg = {
                    id: rumor.id,
                    kind: 15,
                    content: rumor.content,
                    fileMeta,
                    timestamp: rumor.created_at,
                    from: authorPubkey,
                    actualTimestamp: giftWrap.created_at
                };
            } else {
                newMsg = {
                    id: rumor.id,
                    kind: 14,
                    content: rumor.content,
                    timestamp: rumor.created_at,
                    from: authorPubkey,
                    actualTimestamp: giftWrap.created_at
                };
            }
            state.conversations[conversationPubkey].push(newMsg);
            applyPendingReactionsForMessage(conversationPubkey, newMsg);
            state.conversations[conversationPubkey].sort((a, b) => a.timestamp - b.timestamp);
            dbSaveMessage(conversationPubkey, newMsg);

            if (newMsg.timestamp > state.sessionStartedAt) {
                if (state.currentChat !== conversationPubkey || state.currentChatProtocol !== 'nip17') {
                    state.unreadNip17.add(conversationPubkey);
                }
            }

            if (!options.suppressUi) {
                const { updateConversationsList } = await import('./ui.js');
                updateConversationsList();
                if (state.currentChat === conversationPubkey) {
                    queueActiveChatRender(conversationPubkey, { header: true });
                }
                if (!state.userProfiles[conversationPubkey]) {
                    void fetchUserProfile(conversationPubkey).then(() => {
                        queueConversationsListUpdate();
                        queueChatHeaderUpdate(conversationPubkey);
                    });
                }
            }
        } finally {
            // Import lazily from sync to avoid circular dependency
            import('./sync.js').then(({ noteInboxGiftWrapProcessed }) => {
                noteInboxGiftWrapProcessed(giftWrap.created_at);
            });
        }

    } catch (error) {
        // Catch any other unexpected errors (JSON parsing, etc.)
        // Log but don't throw - we want to continue processing other messages
        console.error('Unexpected error processing gift-wrapped message:', error);
        console.error('Error details:', {
            message: error.message,
            giftWrap: giftWrap ? { id: giftWrap.id, kind: giftWrap.kind } : null
        });
        // Return silently - don't let one bad message stop processing others
        return;
    }
}

export function getRumorConversationPubkey(rumor, authorPubkey) {
    let conversationPubkey = authorPubkey;
    if (authorPubkey === state.publicKey) {
        const pTag = Array.isArray(rumor.tags)
            ? rumor.tags.find((t) => t[0] === 'p' && typeof t[1] === 'string' && t[1].length)
            : null;
        if (!pTag) {
            return null;
        }
        conversationPubkey = normalizePubkey(pTag[1]);
    }
    return conversationPubkey;
}

/** First tag value for name (NIP-17 file tags, etc.). */
export function rumorTagValue(tags, name) {
    if (!Array.isArray(tags)) return '';
    const row = tags.find((t) => t[0] === name && typeof t[1] === 'string' && t[1].length);
    return row ? row[1] : '';
}

/** NIP-17 kind 15 file message — content is file URL; tags carry crypto metadata. */
export function parseKind15FileMeta(rumor) {
    const url = typeof rumor.content === 'string' ? rumor.content.trim() : '';
    if (!url) return null;
    const tags = rumor.tags;
    return {
        fileType: rumorTagValue(tags, 'file-type') || 'application/octet-stream',
        url,
        encryptionAlgorithm: rumorTagValue(tags, 'encryption-algorithm'),
        decryptionKey: rumorTagValue(tags, 'decryption-key'),
        decryptionNonce: rumorTagValue(tags, 'decryption-nonce'),
        xHash: rumorTagValue(tags, 'x'),
        thumbUrl: rumorTagValue(tags, 'thumb'),
        dim: rumorTagValue(tags, 'dim'),
        blurhash: rumorTagValue(tags, 'blurhash')
    };
}

export function formatConversationPreview(msg) {
    if (!msg) return 'No messages yet';
    if (msg.kind === 15 && msg.fileMeta) {
        const ft = msg.fileMeta.fileType || '';
        if (ft.startsWith('image/')) return '📷 Photo';
        if (ft.startsWith('audio/')) return '🎵 Audio';
        if (ft.startsWith('video/')) return '🎬 Video';
        return '📎 File';
    }
    const c = typeof msg.content === 'string' ? msg.content : '';
    if (!c) return '—';
    return `${c.substring(0, 50)}${c.length > 50 ? '...' : ''}`;
}

export function lastConversationSortTime(conv) {
    if (!conv || conv.length === 0) {
        return 0;
    }
    return conv[conv.length - 1].timestamp;
}

/**
 * Lightweight render fingerprint so we avoid repainting an unchanged conversation
 * after background repair/backfill queries complete.
 */
export function getConversationFingerprint(pubkey) {
    const conv = state.conversations[pubkey] || [];
    if (!conv.length) {
        return 'empty';
    }
    const parts = [`n:${conv.length}`];
    for (const msg of conv) {
        const rid = msg?.id || '';
        const kind = msg?.kind || 14;
        const ts = msg?.timestamp || 0;
        const rc = msg?.reactions
            ? Object.values(msg.reactions).reduce((sum, bucket) => sum + (bucket?.count || 0), 0)
            : 0;
        parts.push(`${rid}:${kind}:${ts}:r${rc}`);
    }
    return parts.join('|');
}

export async function publishRumorAsGiftWrap(rumor, peerPubkey) {
    // Two-tier resolution:
    //   1. kind 10050 on current relay set
    //   2. NIP-65 kind 10002 inbox relays as last resort
    //   3. Default relay set — contact hasn't published inbox preferences; best-effort delivery
    let recipientInboxRelays = await resolveInboxRelays(peerPubkey);
    if (!recipientInboxRelays.length) {
        console.warn(`No inbox relays found for ${peerPubkey.slice(0, 8)} — publishing to default relays as best-effort delivery`);
        recipientInboxRelays = [...RELAY_URLS];
    }
    const publishRelays = [...new Set(recipientInboxRelays)];
    const relayHint = recipientInboxRelays[0] || null;

    const sealContent = JSON.stringify(rumor);
    const encryptedRumor = await window.nostr.nip44.encrypt(peerPubkey, sealContent);

    const sealTemplate = {
        kind: 13,
        pubkey: state.publicKey,
        created_at: getRandomPastTimestamp(),
        tags: relayHint ? [['p', peerPubkey, relayHint]] : [['p', peerPubkey]],
        content: encryptedRumor
    };

    const signedSeal = await window.nostr.signEvent(sealTemplate);
    const sealToWrap = {
        kind: 13,
        pubkey: signedSeal.pubkey ?? sealTemplate.pubkey,
        created_at: signedSeal.created_at ?? sealTemplate.created_at,
        tags: signedSeal.tags?.length ? signedSeal.tags : sealTemplate.tags,
        content: sealTemplate.content,
        id: signedSeal.id,
        sig: signedSeal.sig
    };
    if (!sealToWrap.id || !sealToWrap.sig) {
        throw new Error('Signing failed: missing id or sig');
    }

    await createAndPublishGiftWrap(sealToWrap, peerPubkey, publishRelays, relayHint, { requireSuccess: true });

    const selfInbox = await resolveInboxRelays(state.publicKey);
    if (selfInbox.length > 0) {
        const selfPublishRelays = [...new Set(selfInbox)];
        await createAndPublishGiftWrap(sealToWrap, state.publicKey, selfPublishRelays, selfInbox[0] || null);
    } else {
        console.warn('Skipping self gift-wrap copy: no kind 10050 inbox relays configured for your key. ' +
            'Sent messages will not survive a page reload. Go to Settings → DM Relays to configure your inbox relays.');
        // Surface a brief status hint so the user knows to act
        const statusText = document.getElementById('statusText');
        if (statusText && !statusText.dataset.selfInboxWarned) {
            statusText.dataset.selfInboxWarned = '1';
            const original = statusText.textContent;
            statusText.textContent = 'No inbox relays — sent messages may disappear on reload';
            statusText.style.color = 'var(--color-warning, #c8a000)';
            setTimeout(() => {
                statusText.textContent = original;
                statusText.style.color = '';
                delete statusText.dataset.selfInboxWarned;
            }, 8000);
        }
    }
}

export async function createAndPublishGiftWrap(seal, recipientPubkey, publishRelays, relayHint, options = {}) {
    // Generate random ephemeral key for this gift wrap
    // Note: Ephemeral keys are temporary and only used for gift wrapping
    // These are NOT user keys - they're generated per message for privacy
    const ephemeralKey = generateSecretKey();
    const ephemeralPubkey = getPublicKey(ephemeralKey);

    const recipientHex = normalizePubkey(recipientPubkey);

    // Encrypt the seal using NIP-44 with the ephemeral key
    // Note: We use nostr-tools nip44 here (not extension) because:
    // 1. The extension's nip44 uses the user's key
    // 2. Gift wrapping requires encryption FROM an ephemeral key TO the recipient
    // 3. Ephemeral keys are temporary and not stored in the extension
    const sealJSON = JSON.stringify(seal);

    // Get conversation key for ephemeral key -> recipient encryption
    // This is the only place we use nostr-tools nip44; all user operations use extension
    const conversationKey = getConversationKey(ephemeralKey, recipientHex);
    const encryptedSeal = nip44Encrypt(sealJSON, conversationKey);

    // Create gift wrap (kind 1059); optional third element on p matches NIP-17 / interop room identity
    const pTag = relayHint ? ['p', recipientHex, relayHint] : ['p', recipientHex];
    const giftWrap = {
        kind: 1059,
        pubkey: ephemeralPubkey,
        created_at: getRandomPastTimestamp(),
        tags: [pTag],
        content: encryptedSeal
    };

    // Sign the gift wrap with the ephemeral key
    const signedGiftWrap = finalizeEvent(giftWrap, ephemeralKey);

    // Publish to all relays
    // Use Promise.any() so we succeed if at least one relay accepts the event
    // This prevents timeout errors if some relays are slow or rejecting
    try {
        const targets = publishRelays?.length ? publishRelays : RELAY_URLS;
        const publishPromises = targets.map(async (url) => {
            try {
                await state.pool.publish([url], signedGiftWrap, { onauth: nostrAuthHandler });
                return { success: true, url };
            } catch (err) {
                console.warn(`Failed to publish to ${url}:`, err);
                throw err; // Re-throw so Promise.any can handle it
            }
        });

        await Promise.any(publishPromises);
        console.log('Gift wrap published successfully to at least one relay');
    } catch (error) {
        if (options.requireSuccess) {
            throw new Error('Failed to publish gift wrap to recipient inbox relays.');
        }
        // If all relays fail for non-required copies, log but keep UI responsive.
        console.warn('Failed to publish optional gift wrap copy to all relays:', error);
    }
}

export async function sendReactionToMessage(message, emoji) {
    if (!state.currentChat || !message?.id) return;
    const normalizedEmoji = normalizeReactionContent(emoji);
    if (!normalizedEmoji) return;

    applyReactionToMessage(message, normalizedEmoji, state.publicKey);
    queueActiveChatRender(state.currentChat);

    try {
        const now = Math.floor(Date.now() / 1000);
        const rumor = {
            kind: 7,
            pubkey: state.publicKey,
            created_at: now,
            tags: [['e', message.id], ['k', String(message.kind || 14)], ['p', state.currentChat]],
            content: normalizedEmoji
        };
        rumor.id = getEventHash(rumor);
        await publishRumorAsGiftWrap(rumor, state.currentChat);
    } catch (error) {
        console.warn('Failed to publish reaction:', error);
    }
}

export function clearPendingImage() {
    if (state.pendingImageObjectUrl) {
        URL.revokeObjectURL(state.pendingImageObjectUrl);
        state.pendingImageObjectUrl = null;
    }
    state.pendingImageUrl = null;
    const card = document.getElementById('chatImagePreview');
    if (card) card.hidden = true;
}

export async function sendMessage() {
    const input = document.getElementById('messageInput');
    const sendBtn = document.getElementById('sendBtn');
    const textContent = input.value.trim();
    const imageUrl = state.pendingImageUrl;

    if (!textContent && !imageUrl) return;
    if (!state.currentChat) return;

    const content = imageUrl
        ? (textContent ? `${textContent}\n${imageUrl}` : imageUrl)
        : textContent;

    if (state.currentChatProtocol === 'nip04') {
        await sendNip04Message(state.currentChat, content);
        input.value = '';
        clearPendingImage();
        return;
    }

    sendBtn.disabled = true;
    sendBtn.innerHTML = '<div class="loading"></div>';

    try {
        const now = Math.floor(Date.now() / 1000);

        // Step 1: Create the rumor (kind 14) — unsigned; NIP-17 requires id + created_at (same as nostr-tools createRumor)
        const rumor = {
            kind: 14,
            pubkey: state.publicKey,
            created_at: now,
            tags: [['p', state.currentChat]],
            content: content
        };
        rumor.id = getEventHash(rumor);
        await publishRumorAsGiftWrap(rumor, state.currentChat);

        // Add to local conversation
        if (!state.conversations[state.currentChat]) {
            state.conversations[state.currentChat] = [];
        }

        state.conversations[state.currentChat].push({
            id: rumor.id,
            kind: 14,
            content: content,
            timestamp: now,
            from: state.publicKey
        });

        const { displayMessages, updateConversationsList } = await import('./ui.js');
        displayMessages(state.currentChat);
        updateConversationsList();
        input.value = '';
        clearPendingImage();

    } catch (error) {
        alert('Failed to send message: ' + error.message);
        console.error(error);
    } finally {
        sendBtn.disabled = false;
        sendBtn.innerHTML = '<svg viewBox="0 0 24 24"><path d="M2.01 21L23 12 2.01 3 2 10l15 2-15 2z"/></svg>';
    }
}

export async function sendImageMessage(file) {
    if (!state.currentChat) return;
    if (file.size > MAX_IMAGE_UPLOAD_BYTES) {
        alert(`Image too large (max ${MAX_IMAGE_UPLOAD_BYTES / 1024 / 1024} MB).`);
        return;
    }

    // Show card immediately with spinner while upload is in flight
    const objectUrl = URL.createObjectURL(file);
    state.pendingImageObjectUrl = objectUrl;

    const card = document.getElementById('chatImagePreview');
    const thumb = document.getElementById('chatImagePreviewThumb');
    const spinner = document.getElementById('chatImagePreviewSpinner');
    const filenameEl = document.getElementById('chatImagePreviewFilename');
    const sendBtn = document.getElementById('sendBtn');
    const imageUploadBtn = document.getElementById('imageUploadBtn');

    if (filenameEl) filenameEl.textContent = file.name;
    if (thumb) thumb.hidden = true;
    if (spinner) spinner.hidden = false;
    if (card) card.hidden = false;
    if (sendBtn) sendBtn.disabled = true;
    if (imageUploadBtn) imageUploadBtn.disabled = true;

    try {
        const url = await uploadImageToNostr(file);
        state.pendingImageUrl = url;
        // Swap spinner for thumbnail
        if (thumb) { thumb.src = objectUrl; thumb.hidden = false; }
        if (spinner) spinner.hidden = true;
        if (sendBtn) sendBtn.disabled = false;
    } catch (e) {
        clearPendingImage();
        alert('Upload failed: ' + e.message);
    } finally {
        if (imageUploadBtn) imageUploadBtn.disabled = false;
    }
}

// ─── NIP-04 (kind 4) helpers ──────────────────────────────────────────────────

async function decryptNip04(ciphertext, theirPubkey) {
    return window.nostr.nip04.decrypt(theirPubkey, ciphertext);
}

async function encryptNip04(plaintext, theirPubkey) {
    return window.nostr.nip04.encrypt(theirPubkey, plaintext);
}

export async function handleKind4Event(event) {
    if (!event?.id || !event?.pubkey) return;
    if (state.seenKind4EventIds.has(event.id)) return;
    state.seenKind4EventIds.add(event.id);
    dbMarkKind4Seen(event.id);

    const peerPubkey = event.pubkey === state.publicKey
        ? (event.tags.find(t => t[0] === 'p')?.[1] ?? null)
        : event.pubkey;
    if (!peerPubkey) return;

    let content;
    try {
        content = await decryptNip04(event.content, peerPubkey);
    } catch (e) {
        console.warn('NIP-04 decrypt failed:', event.id, e);
        return;
    }

    const msg = {
        id: event.id,
        kind: 4,
        content,
        timestamp: event.created_at,
        from: event.pubkey,
    };

    if (!state.nip04Conversations[peerPubkey]) state.nip04Conversations[peerPubkey] = [];
    if (state.nip04Conversations[peerPubkey].some(m => m.id === msg.id)) return;
    state.nip04Conversations[peerPubkey].push(msg);
    state.nip04Conversations[peerPubkey].sort((a, b) => a.timestamp - b.timestamp);

    dbSaveNip04Message(peerPubkey, msg);

    if (!state.userProfiles[peerPubkey]) fetchUserProfile(peerPubkey);

    if (msg.timestamp > state.sessionStartedAt) {
        if (state.activeConversationTab !== 'nip04') {
            import('./ui.js').then(({ setNip04Unread }) => setNip04Unread(true));
        }
        if (state.currentChat !== peerPubkey || state.currentChatProtocol !== 'nip04') {
            state.unreadNip04.add(peerPubkey);
        }
    }
    queueConversationsListUpdate();
    if (state.currentChat === peerPubkey && state.currentChatProtocol === 'nip04') {
        queueActiveChatRender(peerPubkey);
    }
}

export async function sendNip04Message(peerPubkey, text) {
    const sendBtn = document.getElementById('sendBtn');
    if (sendBtn) {
        sendBtn.disabled = true;
        sendBtn.innerHTML = '<div class="loading"></div>';
    }
    try {
        const ciphertext = await encryptNip04(text, peerPubkey);
        const now = Math.floor(Date.now() / 1000);
        const unsigned = {
            kind: 4,
            pubkey: state.publicKey,
            created_at: now,
            tags: [['p', peerPubkey]],
            content: ciphertext,
        };
        const signed = await window.nostr.signEvent(unsigned);
        state.pool.publish(RELAY_URLS, signed);

        const localMsg = { id: signed.id, kind: 4, content: text, timestamp: now, from: state.publicKey };
        if (!state.nip04Conversations[peerPubkey]) state.nip04Conversations[peerPubkey] = [];
        state.nip04Conversations[peerPubkey].push(localMsg);
        state.seenKind4EventIds.add(signed.id);
        dbSaveNip04Message(peerPubkey, localMsg);
        dbMarkKind4Seen(signed.id);

        const { displayNip04Messages, updateConversationsList } = await import('./ui.js');
        displayNip04Messages(peerPubkey);
        updateConversationsList();
    } catch (e) {
        alert('Failed to send NIP-04 message: ' + e.message);
        console.error(e);
    } finally {
        if (sendBtn) {
            sendBtn.disabled = false;
            sendBtn.innerHTML = '<svg viewBox="0 0 24 24"><path d="M2.01 21L23 12 2.01 3 2 10l15 2-15 2z"/></svg>';
        }
    }
}

export function subscribeToNip04Messages() {
    if (!state.pool || !state.publicKey) return;
    if (typeof window.nostr?.nip04?.decrypt !== 'function') {
        console.info('NIP-04: window.nostr.nip04 not available, skipping subscription');
        return;
    }

    const since = Math.floor(Date.now() / 1000);
    const relays = getReadRelayUrlsUnsorted();
    const onEvent = (ev) => handleKind4Event(ev).catch((e) => console.warn('NIP-04 event error:', e));

    const subReceived = state.pool.subscribe(relays, { kinds: [4], '#p': [state.publicKey], since }, {
        onevent: onEvent,
    });
    const subSent = state.pool.subscribe(relays, { kinds: [4], authors: [state.publicKey], since }, {
        onevent: onEvent,
    });
    state.kind4Subscription = [subReceived, subSent];
}
