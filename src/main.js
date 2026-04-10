import { SimplePool, generateSecretKey, getPublicKey, getEventHash, finalizeEvent } from 'nostr-tools';
import * as nip19 from 'nostr-tools/nip19';
// Note: nip44 is used for both ephemeral key operations and user key operations
// We check if extension provides nip44, otherwise fall back to library (but need private key access)
import { encrypt as nip44Encrypt, decrypt as nip44Decrypt, getConversationKey } from 'nostr-tools/nip44';

// Relay URLs to connect to
const RELAY_URLS = [
    'wss://relay.0xchat.com',
    'wss://relay.damus.io',
    'wss://relay.primal.net',
    'wss://auth.nostr1.com'
];

let pool = null;
let publicKey = null;
let conversations = {};
let currentChat = null;
let userProfiles = {}; // Store user profiles (display names, etc.)
let messageSubscription = null; // Store the message subscription
/** Relays used for DM subscribe/publish: default list plus our kind 10050 inbox relays after connect */
let dmRelayUrls = [...RELAY_URLS];

// Check if NIP-07 extension is available
function hasNostrExtension() {
    return typeof window.nostr !== 'undefined';
}

async function connectWithExtension() {
    if (!hasNostrExtension()) {
        alert('No Nostr extension detected!\n\nPlease install a NIP-07 compatible extension:\n\n• Alby (recommended) - https://getalby.com\n• nos2x - Lightweight extension\n• Flamingo - Feature-rich\n• horse - Privacy-focused\n\nAfter installing, refresh this page and try again.');
        return;
    }

    try {
        // Get public key from extension
        publicKey = await window.nostr.getPublicKey();

        // Check if extension supports NIP-44 (required for this app)
        if (!window.nostr.nip44 || !window.nostr.nip44.encrypt || !window.nostr.nip44.decrypt) {
            alert('Your Nostr extension does not support NIP-44 encryption/decryption.\n\n' +
                  'This app requires NIP-44 support for secure messaging.\n\n' +
                  'Please use an extension that supports NIP-44:\n' +
                  '• Alby (recommended) - https://getalby.com\n' +
                  '• Or another extension with NIP-44 support\n\n' +
                  'After installing/updating, refresh this page.');
            return;
        }

        // Create pool and connect to multiple relays
        pool = new SimplePool();
        
        // Connect to all relays
        document.getElementById('statusText').textContent = 'Connecting to relays...';
        const connectPromises = RELAY_URLS.map(async (url) => {
            try {
                const relay = await pool.ensureRelay(url);
                console.log('Connected to relay:', url);
                return { url, success: true, relay };
            } catch (error) {
                console.warn('Failed to connect to relay:', url, error);
                return { url, success: false, error };
            }
        });
        
        const results = await Promise.allSettled(connectPromises);
        const successfulConnections = results.filter(r => r.status === 'fulfilled' && r.value.success).length;

        document.getElementById('statusDot').classList.add('connected');
        document.getElementById('statusText').textContent = `Connected to ${successfulConnections}/${RELAY_URLS.length} relays`;
        document.getElementById('connectionSetup').style.display = 'none';
        document.getElementById('newDmSection').style.display = 'block';

        await mergeOwnInboxRelays();

        // Wait a bit for connections to stabilize, then subscribe
        setTimeout(() => {
            subscribeToMessages();
        }, 1000);

    } catch (error) {
        alert('Connection failed: ' + error.message);
        console.error(error);
    }
}

// Fetch user profile (kind 0) to get display name
async function fetchUserProfile(pubkey) {
    if (userProfiles[pubkey]) {
        return userProfiles[pubkey]; // Already cached
    }

    try {
        // Subscribe to kind 0 events for this user
        // Note: pool.subscribe takes a single filter object, not an array
        return new Promise((resolve) => {
            const sub = pool.subscribe(RELAY_URLS, {
                kinds: [0],
                authors: [pubkey],
                limit: 1
            }, {
                onevent(event) {
                    try {
                        const profile = JSON.parse(event.content);
                        userProfiles[pubkey] = {
                            name: profile.name || profile.display_name || null,
                            display_name: profile.display_name || profile.name || null,
                            picture: profile.picture || null,
                            about: profile.about || null
                        };
                        sub.close();
                        resolve(userProfiles[pubkey]);
                    } catch (err) {
                        console.error('Failed to parse profile', err);
                    }
                },
                oneose() {
                    // If no events found, set default
                    if (!userProfiles[pubkey]) {
                        userProfiles[pubkey] = { name: null, display_name: null, picture: null, about: null };
                    }
                    resolve(userProfiles[pubkey]);
                }
            });

            // Timeout after 3 seconds
            setTimeout(() => {
                if (!userProfiles[pubkey]) {
                    userProfiles[pubkey] = { name: null, display_name: null, picture: null, about: null };
                    sub.close();
                    resolve(userProfiles[pubkey]);
                }
            }, 3000);
        });
    } catch (error) {
        console.error('Failed to fetch profile for', pubkey, error);
        userProfiles[pubkey] = { name: null, display_name: null, picture: null, about: null };
        return userProfiles[pubkey];
    }
}

// Get display name for a pubkey (with fallback to short pubkey)
function getDisplayName(pubkey) {
    const profile = userProfiles[pubkey];
    if (profile && (profile.display_name || profile.name)) {
        return profile.display_name || profile.name;
    }
    // Fallback to short pubkey
    return pubkey.slice(0, 8) + '...' + pubkey.slice(-8);
}

/** Kind 10050: preferred relays to receive NIP-17 gift wraps (NIP-17 publishing + our subscription) */
async function fetchKind10050Relays(authorPubkey) {
    try {
        const queryRelays = dmRelayUrls?.length ? dmRelayUrls : RELAY_URLS;
        const ev = await pool.get(queryRelays, { kinds: [10050], authors: [authorPubkey] });
        if (!ev?.tags?.length) return [];
        return ev.tags.filter((t) => t[0] === 'relay' && typeof t[1] === 'string' && t[1].length > 0).map((t) => t[1]);
    } catch (e) {
        console.warn('fetchKind10050Relays failed:', e);
        return [];
    }
}

async function mergeOwnInboxRelays() {
    const mine = await fetchKind10050Relays(publicKey);
    if (!mine.length) {
        dmRelayUrls = [...RELAY_URLS];
        return;
    }
    dmRelayUrls = [...new Set([...RELAY_URLS, ...mine])];
    await Promise.allSettled(
        mine.map(async (url) => {
            try {
                await pool.ensureRelay(url);
            } catch (err) {
                console.warn('Could not connect to inbox relay:', url, err);
            }
        })
    );
}

// Generate random timestamp within 2 days in the past
function getRandomPastTimestamp() {
    const now = Math.floor(Date.now() / 1000);
    const twoDaysAgo = now - (2 * 24 * 60 * 60);
    return twoDaysAgo + Math.floor(Math.random() * (2 * 24 * 60 * 60));
}

function subscribeToMessages() {
    // Subscribe to kind 1059 (gift-wrapped) events tagged with our pubkey
    // SimplePool.subscribe automatically queries all connected relays
    // Store the subscription so it stays alive
    console.log('Setting up subscription for publicKey:', publicKey);
    console.log('Subscribing to relays:', dmRelayUrls);
    
    let eventCount = 0;
    const seenEventIds = new Set(); // Track seen events to detect duplicates
    
    // Create filter for gift-wrapped messages (kind 1059) tagged with our pubkey
    // Note: pool.subscribe takes a single filter object, not an array
    // Remove 'since' to get all historical messages, not just recent ones
    const filter = {
        kinds: [1059],
        '#p': [publicKey]
    };
    console.log('Subscription filter:', JSON.stringify(filter, null, 2));
    
    messageSubscription = pool.subscribe(dmRelayUrls, filter, {
        onevent(event) {
            eventCount++;
            const isDuplicate = seenEventIds.has(event.id);
            seenEventIds.add(event.id);
            
            console.log(`✅ Received gift-wrapped message #${eventCount}${isDuplicate ? ' (duplicate)' : ''}:`, {
                id: event.id,
                kind: event.kind,
                created_at: new Date(event.created_at * 1000).toISOString(),
                tags: event.tags
            });
            
            // Only process if not a duplicate
            if (!isDuplicate) {
                // Handle message asynchronously - don't let errors in one message stop others
                handleGiftWrappedMessage(event).catch(error => {
                    console.error('Error in handleGiftWrappedMessage (non-blocking):', error);
                });
            }
        },
        oneose() {
            console.log(`📭 EOSE (End of Stored Events) - received ${eventCount} total events, ${seenEventIds.size} unique`);
        }
    });
    
    console.log('✅ Subscription active - listening for messages on', dmRelayUrls.length, 'relays');
    console.log('💡 Querying all historical messages (no time limit)');
}

async function handleGiftWrappedMessage(giftWrap) {
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

        // Step 3: Decrypt the seal to get the rumor (kind 14)
        // Seal is encrypted FROM sender TO our public key
        console.log('Decrypting seal from sender:', seal.pubkey);
        let rumorJSON;
        try {
            rumorJSON = await window.nostr.nip44.decrypt(
                seal.pubkey,
                seal.content
            );
            console.log('Successfully decrypted seal');
        } catch (decryptError) {
            // If seal decryption fails, skip this message
            console.warn('Failed to decrypt seal (may not be for us or wrong encryption):', {
                error: decryptError.message,
                eventId: giftWrap.id,
                senderPubkey: seal.pubkey
            });
            return; // Skip this message, continue with others
        }
        
        const rumor = JSON.parse(rumorJSON);
        console.log('Unwrapped rumor:', { kind: rumor.kind, pubkey: rumor.pubkey, content: rumor.content?.substring(0, 50) });
        
        // Step 4: Verify it's a chat message (kind 14)
        if (rumor.kind !== 14) {
            console.error('Expected kind 14 rumor, got:', rumor.kind);
            return;
        }

        // Step 5: Verify the sender
        if (seal.pubkey !== rumor.pubkey) {
            console.error('Sender pubkey mismatch - potential impersonation attempt');
            return;
        }

        const senderPubkey = rumor.pubkey;
        
        // Initialize conversation if needed
        if (!conversations[senderPubkey]) {
            conversations[senderPubkey] = [];
        }

        // Add message to conversation
        conversations[senderPubkey].push({
            content: rumor.content,
            timestamp: rumor.created_at,
            from: senderPubkey,
            actualTimestamp: giftWrap.created_at
        });

        conversations[senderPubkey].sort((a, b) => a.timestamp - b.timestamp);

        // Fetch user profile if we don't have it
        if (!userProfiles[senderPubkey]) {
            await fetchUserProfile(senderPubkey);
        }

        updateConversationsList();
        if (currentChat === senderPubkey) {
            displayMessages(senderPubkey);
            updateChatHeader(senderPubkey);
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

function updateConversationsList() {
    const list = document.getElementById('conversationsList');
    list.innerHTML = '';

    Object.keys(conversations).sort((a, b) => {
        const lastA = conversations[a][conversations[a].length - 1];
        const lastB = conversations[b][conversations[b].length - 1];
        return lastB.timestamp - lastA.timestamp;
    }).forEach(pubkey => {
        const conv = conversations[pubkey];
        const lastMsg = conv[conv.length - 1];

        const item = document.createElement('div');
        item.className = 'conversation-item' + (currentChat === pubkey ? ' active' : '');
        item.onclick = () => openChat(pubkey);

        const displayName = getDisplayName(pubkey);
        const shortPubkey = pubkey.slice(0, 8) + '...' + pubkey.slice(-8);
        const dateIndicator = formatConversationDate(lastMsg.timestamp);
        item.innerHTML = `
            <div style="display: flex; justify-content: space-between; align-items: flex-start; margin-bottom: 4px;">
                <div class="conversation-pubkey">${displayName}</div>
                <div class="conversation-date">${dateIndicator}</div>
            </div>
            <div class="conversation-preview">${lastMsg.content.substring(0, 50)}${lastMsg.content.length > 50 ? '...' : ''}</div>
        `;

        list.appendChild(item);
    });
}

async function startNewConversation() {
    let pubkeyInput = document.getElementById('newDmPubkey').value.trim();

    if (!pubkeyInput) {
        alert('Please enter a recipient pubkey');
        return;
    }

    try {
        if (pubkeyInput.startsWith('npub')) {
            const decoded = nip19.decode(pubkeyInput);
            pubkeyInput = decoded.data;
        }

        if (!conversations[pubkeyInput]) {
            conversations[pubkeyInput] = [];
        }

        // Fetch user profile
        await fetchUserProfile(pubkeyInput);

        openChat(pubkeyInput);
        document.getElementById('newDmPubkey').value = '';
    } catch (error) {
        alert('Invalid pubkey: ' + error.message);
    }
}

function openChat(pubkey) {
    currentChat = pubkey;
    document.getElementById('emptyState').style.display = 'none';
    document.getElementById('chatView').style.display = 'flex';

    updateChatHeader(pubkey);
    displayMessages(pubkey);
    updateConversationsList();
}

// Update chat header with display name
function updateChatHeader(pubkey) {
    const displayName = getDisplayName(pubkey);
    const shortPubkey = pubkey.slice(0, 16) + '...' + pubkey.slice(-16);
    
    // Show display name, or short pubkey if no name available
    const profile = userProfiles[pubkey];
    if (profile && (profile.display_name || profile.name)) {
        document.getElementById('currentChatPubkey').textContent = displayName;
    } else {
        document.getElementById('currentChatPubkey').textContent = shortPubkey;
    }
}

// Format timestamp with date and time
function formatTimestamp(timestamp) {
    const date = new Date(timestamp * 1000);
    const now = new Date();
    const today = new Date(now.getFullYear(), now.getMonth(), now.getDate());
    const messageDate = new Date(date.getFullYear(), date.getMonth(), date.getDate());
    
    // Check if message is from today
    if (messageDate.getTime() === today.getTime()) {
        // Today: show only time
        return date.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
    } else {
        // Not today: show date and time
        return date.toLocaleString([], { 
            month: 'short', 
            day: 'numeric', 
            hour: '2-digit', 
            minute: '2-digit' 
        });
    }
}

// Format date for separators (e.g., "Today", "Yesterday", "Dec 25")
function formatDateSeparator(timestamp) {
    const date = new Date(timestamp * 1000);
    const now = new Date();
    const today = new Date(now.getFullYear(), now.getMonth(), now.getDate());
    const yesterday = new Date(today);
    yesterday.setDate(yesterday.getDate() - 1);
    const messageDate = new Date(date.getFullYear(), date.getMonth(), date.getDate());
    
    if (messageDate.getTime() === today.getTime()) {
        return 'Today';
    } else if (messageDate.getTime() === yesterday.getTime()) {
        return 'Yesterday';
    } else {
        return date.toLocaleDateString([], { month: 'long', day: 'numeric', year: date.getFullYear() !== now.getFullYear() ? 'numeric' : undefined });
    }
}

// Format date for conversation list (shorter format)
function formatConversationDate(timestamp) {
    const date = new Date(timestamp * 1000);
    const now = new Date();
    const today = new Date(now.getFullYear(), now.getMonth(), now.getDate());
    const yesterday = new Date(today);
    yesterday.setDate(yesterday.getDate() - 1);
    const messageDate = new Date(date.getFullYear(), date.getMonth(), date.getDate());
    
    if (messageDate.getTime() === today.getTime()) {
        // Today: show time
        return date.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
    } else if (messageDate.getTime() === yesterday.getTime()) {
        return 'Yesterday';
    } else {
        // Older: show short date
        const daysDiff = Math.floor((today - messageDate) / (1000 * 60 * 60 * 24));
        if (daysDiff < 7) {
            // Within a week: show day name
            return date.toLocaleDateString([], { weekday: 'short' });
        } else if (date.getFullYear() === now.getFullYear()) {
            // This year: show month and day
            return date.toLocaleDateString([], { month: 'short', day: 'numeric' });
        } else {
            // Older: show month, day, year
            return date.toLocaleDateString([], { month: 'short', day: 'numeric', year: '2-digit' });
        }
    }
}

function displayMessages(pubkey) {
    const container = document.getElementById('messagesContainer');
    container.innerHTML = '';

    if (!conversations[pubkey]) return;

    let lastDate = null;

    conversations[pubkey].forEach((msg, index) => {
        const msgDate = new Date(msg.timestamp * 1000);
        const currentDate = new Date(msgDate.getFullYear(), msgDate.getMonth(), msgDate.getDate());
        
        // Add date separator if this is a new day
        if (lastDate === null || currentDate.getTime() !== lastDate.getTime()) {
            const dateSeparator = document.createElement('div');
            dateSeparator.className = 'date-separator';
            dateSeparator.textContent = formatDateSeparator(msg.timestamp);
            container.appendChild(dateSeparator);
            lastDate = currentDate;
        }

        const div = document.createElement('div');
        div.className = 'message ' + (msg.from === publicKey ? 'sent' : 'received');
        
        const time = formatTimestamp(msg.timestamp);
        div.innerHTML = `
            ${msg.content}
            <div class="message-time">${time}</div>
        `;

        container.appendChild(div);
    });

    container.scrollTop = container.scrollHeight;
}

async function sendMessage() {
    const input = document.getElementById('messageInput');
    const sendBtn = document.getElementById('sendBtn');
    const content = input.value.trim();

    if (!content || !currentChat) return;

    sendBtn.disabled = true;
    sendBtn.innerHTML = '<div class="loading"></div>';

    try {
        const now = Math.floor(Date.now() / 1000);

        const recipientInboxRelays = await fetchKind10050Relays(currentChat);
        const publishRelays =
            recipientInboxRelays.length > 0
                ? [...new Set([...recipientInboxRelays, ...RELAY_URLS])]
                : [...RELAY_URLS];
        const relayHint = recipientInboxRelays[0] || null;

        // Step 1: Create the rumor (kind 14) — unsigned; NIP-17 requires id + created_at (same as nostr-tools createRumor)
        const rumor = {
            kind: 14,
            pubkey: publicKey,
            created_at: now,
            tags: relayHint ? [['p', currentChat, relayHint]] : [['p', currentChat]],
            content: content
        };
        rumor.id = getEventHash(rumor);

        // Step 2: Seal the rumor (kind 13)
        const sealContent = JSON.stringify(rumor);
        // Use extension's nip44 (we already checked it exists at connection time)
        const encryptedRumor = await window.nostr.nip44.encrypt(currentChat, sealContent);

        const seal = {
            kind: 13,
            pubkey: publicKey,
            created_at: getRandomPastTimestamp(),
            tags: [],
            content: encryptedRumor
        };

        // Sign the seal with extension
        const signedSeal = await window.nostr.signEvent(seal);
        seal.id = signedSeal.id;
        seal.sig = signedSeal.sig;

        // Step 3: Gift wrap for recipient (publish to their inbox relays per NIP-17 + defaults)
        await createAndPublishGiftWrap(seal, currentChat, publishRelays, relayHint);

        // Step 4: Gift wrap for sender (ourselves) — use our inbox + defaults so our other clients see the same thread
        const selfInbox = await fetchKind10050Relays(publicKey);
        const selfPublishRelays =
            selfInbox.length > 0 ? [...new Set([...selfInbox, ...RELAY_URLS])] : publishRelays;
        // Sender copy: only use our own inbox relay hint, not the peer's (avoids wrong room on our other clients)
        await createAndPublishGiftWrap(seal, publicKey, selfPublishRelays, selfInbox[0] || null);

        // Add to local conversation
        if (!conversations[currentChat]) {
            conversations[currentChat] = [];
        }

        conversations[currentChat].push({
            content: content,
            timestamp: now,
            from: publicKey
        });

        displayMessages(currentChat);
        updateConversationsList();
        input.value = '';

    } catch (error) {
        alert('Failed to send message: ' + error.message);
        console.error(error);
    } finally {
        sendBtn.disabled = false;
        sendBtn.innerHTML = '<svg viewBox="0 0 24 24"><path d="M2.01 21L23 12 2.01 3 2 10l15 2-15 2z"/></svg>';
    }
}

async function createAndPublishGiftWrap(seal, recipientPubkey, publishRelays, relayHint) {
    // Generate random ephemeral key for this gift wrap
    // Note: Ephemeral keys are temporary and only used for gift wrapping
    // These are NOT user keys - they're generated per message for privacy
    const ephemeralKey = generateSecretKey();
    const ephemeralPubkey = getPublicKey(ephemeralKey);

    // Encrypt the seal using NIP-44 with the ephemeral key
    // Note: We use nostr-tools nip44 here (not extension) because:
    // 1. The extension's nip44 uses the user's key
    // 2. Gift wrapping requires encryption FROM an ephemeral key TO the recipient
    // 3. Ephemeral keys are temporary and not stored in the extension
    const sealJSON = JSON.stringify(seal);
    
    // Get conversation key for ephemeral key -> recipient encryption
    // This is the only place we use nostr-tools nip44; all user operations use extension
    const conversationKey = getConversationKey(ephemeralKey, recipientPubkey);
    const encryptedSeal = nip44Encrypt(sealJSON, conversationKey);

    // Create gift wrap (kind 1059); optional third element on p matches NIP-17 / interop room identity
    const pTag = relayHint ? ['p', recipientPubkey, relayHint] : ['p', recipientPubkey];
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
                await pool.publish([url], signedGiftWrap);
                return { success: true, url };
            } catch (err) {
                console.warn(`Failed to publish to ${url}:`, err);
                throw err; // Re-throw so Promise.any can handle it
            }
        });
        
        await Promise.any(publishPromises);
        console.log('Gift wrap published successfully to at least one relay');
    } catch (error) {
        // If all relays fail, log but don't throw - we still want to show the message locally
        console.warn('Failed to publish gift wrap to all relays:', error);
        // Don't throw - allow the message to appear locally even if publish fails
    }
}

// Make functions available globally for onclick handlers
window.connectWithExtension = connectWithExtension;
window.startNewConversation = startNewConversation;
window.sendMessage = sendMessage;

// Initialize DOM event listeners when DOM is ready
document.addEventListener('DOMContentLoaded', function() {
    const messageInput = document.getElementById('messageInput');
    if (messageInput) {
        // Auto-resize textarea
        messageInput.addEventListener('input', function() {
            this.style.height = 'auto';
            this.style.height = Math.min(this.scrollHeight, 150) + 'px';
        });

        // Send on Enter
        messageInput.addEventListener('keydown', function(e) {
            if (e.key === 'Enter' && !e.shiftKey) {
                e.preventDefault();
                sendMessage();
            }
        });
    }
});

