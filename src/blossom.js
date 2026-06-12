import { getEventHash } from 'nostr-tools';

import { state } from './state.js';
import { DEFAULT_BLOSSOM_SERVERS, NOSTR_BUILD_UPLOAD_URL } from './constants.js';

async function sha256Hex(buffer) {
    const hash = await crypto.subtle.digest('SHA-256', buffer);
    return Array.from(new Uint8Array(hash)).map(b => b.toString(16).padStart(2, '0')).join('');
}

async function blossomUpload(file, serverUrl, sha256hex) {
    const now = Math.floor(Date.now() / 1000);
    const authEvent = {
        kind: 24242,
        pubkey: state.publicKey,
        created_at: now,
        tags: [
            ['t', 'upload'],
            ['x', sha256hex],
            ['expiration', String(now + 600)]
        ],
        content: `Upload ${file.name}`
    };
    authEvent.id = getEventHash(authEvent);
    const signed = await window.nostr.signEvent(authEvent);
    const token = btoa(JSON.stringify(signed));

    const res = await fetch(`${serverUrl}/upload`, {
        method: 'PUT',
        headers: {
            'Authorization': `Nostr ${token}`,
            'Content-Type': file.type || 'application/octet-stream'
        },
        body: file
    });
    if (!res.ok) throw new Error(`Blossom ${serverUrl}: HTTP ${res.status}`);
    const json = await res.json();
    const url = json?.url;
    if (!url) throw new Error(`Blossom ${serverUrl}: no url in response`);
    return url;
}

async function nostrBuildUpload(file) {
    const form = new FormData();
    form.append('fileToUpload', file);
    const res = await fetch(NOSTR_BUILD_UPLOAD_URL, { method: 'POST', body: form });
    if (!res.ok) throw new Error(`nostr.build: HTTP ${res.status}`);
    const json = await res.json();
    const url = json?.data?.[0]?.url;
    if (!url) throw new Error('nostr.build returned no URL');
    return url;
}

export async function uploadImageToNostr(file) {
    const servers = state.blossomServers?.length ? state.blossomServers : DEFAULT_BLOSSOM_SERVERS;
    const buf = await file.arrayBuffer();
    const hash = await sha256Hex(buf);

    for (const server of servers) {
        try {
            return await blossomUpload(file, server, hash);
        } catch (e) {
            console.warn('Blossom upload failed:', server, e);
        }
    }

    return await nostrBuildUpload(file);
}
