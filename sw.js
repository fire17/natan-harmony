/* Harmony PWA service worker.
   - App shell (html / js / css / worklets / icons): cached at install, served stale-while-revalidate (works offline,
     picks up a new version on the next start). VERSION bumps on every publish (publish-pwa.sh stamps it).
   - Song data (songs/<id>/…, songs/index.json): the songs the user imported live in Cache Storage
     "harmony-songs-v1" (web-bridge.js writes it) and are served from there; anything else under songs/ is
     network-first. No song is part of the published site.
   No key, token or secret is in this file. */
const VERSION = '20261101205145-bdcdbaa1';
const SHELL = 'harmony-shell-' + VERSION, SONGS = 'harmony-songs-v1';
const FILES = ['./', 'index.html', 'web-bridge.js', 'app.js', 'pitch.js', 'voice.js', 'clean.js', 'style.css',
  'stretch-worklet.js', 'fx-worklet.js', 'rec-worklet.js', 'practice-worklet.js', 'practice-pitch.js',
  'vendor/ogg-opus-decoder.min.js', 'LICENSES.txt', 'manifest.webmanifest', 'icons/icon-192.png', 'icons/icon-512.png', 'icons/apple-touch-icon.png'];

self.addEventListener('install', (e) => {
  e.waitUntil(caches.open(SHELL).then((c) => c.addAll(FILES.map((f) => new Request(f, { cache: 'reload' })))).then(() => self.skipWaiting()));
});
self.addEventListener('activate', (e) => {
  e.waitUntil(caches.keys().then((ks) => Promise.all(ks.filter((k) => k.startsWith('harmony-shell-') && k !== SHELL).map((k) => caches.delete(k))))
    .then(() => self.clients.claim()));
});
self.addEventListener('fetch', (e) => {
  const req = e.request; if (req.method !== 'GET') return;
  const url = new URL(req.url); if (url.origin !== location.origin) return; // (LRCLIB etc.: straight to the network)
  const base = new URL('./', self.registration.scope).pathname;
  if (url.pathname.startsWith(base + 'songs/')) { e.respondWith(song(req, url)); return; }
  e.respondWith(shell(e, req, url));
});
async function song(req, url) {
  const c = await caches.open(SONGS), hit = await c.match(url.pathname);
  if (hit) return hit;
  if (url.pathname.endsWith('/songs/index.json')) return new Response('{"songs":[]}', { headers: { 'Content-Type': 'application/json' } });
  try { return await fetch(req); } catch (err) { return new Response('', { status: 504 }); }
}
async function shell(e, req, url) {
  const c = await caches.open(SHELL);
  const key = req.mode === 'navigate' ? 'index.html' : url.pathname.replace(new URL('./', self.registration.scope).pathname, '') || 'index.html';
  const hit = await c.match(key) || await c.match(req, { ignoreSearch: req.mode === 'navigate' });
  const net = fetch(req).then((r) => { if (r.ok && r.type === 'basic') c.put(req.mode === 'navigate' ? 'index.html' : req, r.clone()); return r; });
  if (hit) { e.waitUntil(net.catch(() => {})); return hit; }
  return net.catch(() => new Response('offline', { status: 503 }));
}
