/* Harmony PWA bridge (iPhone / any browser) — loaded BEFORE app.js; app.js itself is the APK's, byte for byte.

   app.js feature-detects every native call on window.Android (typeof … === 'function'). This file defines only the
   ones that have an honest web equivalent, so app.js takes the same paths it takes on the phone:
     - importPick / importStatus      -> "📥 ייבוא שיר": a .hsong picked from Files, checked like SongPacks.kt
                                         (stored zip, pack.json first, safe paths, every song file's size + sha256)
                                         and kept in Cache Storage; songs/<id>/… and songs/index.json are served
                                         from there (fetch below + sw.js), the same URLs the Android side serves.
     - songDelete / packJob           -> 🗑️ removes a song's audio from this device (takes + settings stay, as on Android)
     - lyricsLookup / lyricsJob / netOnline -> "🎤 טעינת מילים": LyricsLookup.kt ported (public LRCLIB API, no key)
     - setState / setNow              -> no-ops (the page already drives navigator.mediaSession)
   NOT defined on purpose (the page hides / falls back by itself):
     - songSearch & co: the relay needs an enrollment key that must never be in a public page (SongSearch.kt)
     - recStart & co (native capture): recording uses the page's own getUserMedia + AudioWorklet path
     - libState / packCommit (the song-folder packs): a browser has no shared folder; takes stay in IndexedDB
     - shareBegin: "שלח לי" downloads the files (the page's browser path)
   No key, token or secret of any kind is in this file. */
(() => {
  'use strict';
  if (typeof window.Android !== 'undefined') return; // inside the real APK: never shadow the native bridge

  const SCOPE = new URL('./', location.href);           // the app's folder (GitHub Pages root, or a sub-path)
  const SONGS = new URL('songs/', SCOPE).pathname;      // "/songs/"
  const CACHE = 'harmony-songs-v1';                     // imported songs (sw.js reads the same cache)
  const APP_CODE = 42;                                  // = the APK's versionCode this page matches (pack.json minApp)
  const IOS = /iP(hone|ad|od)/.test(navigator.userAgent) || (navigator.platform === 'MacIntel' && navigator.maxTouchPoints > 1);
  const PWA = { log: [] };

  // ---------------------------------------------------------------- songs storage (Cache Storage)
  const songUrl = (id, path) => SONGS + id + '/' + path;
  const typeOf = (p) => (/\.json$/.test(p) ? 'application/json' : /\.opus$/.test(p) ? 'audio/ogg' : 'application/octet-stream');
  const jsonResp = (o) => new Response(JSON.stringify(o), { headers: { 'Content-Type': 'application/json' } });
  async function libRead() {
    try { const c = await caches.open(CACHE); const r = await c.match(SONGS + 'index.json'); if (r) { const j = await r.json(); if (j && Array.isArray(j.songs)) return j; } } catch (e) { /* none */ }
    return { songs: [] };
  }
  async function libWrite(lib) { const c = await caches.open(CACHE); await c.put(SONGS + 'index.json', jsonResp(lib)); }

  // songs/* for the page: the imported copy; songs/index.json = the library (empty when nothing was imported)
  async function songFetch(path, init) {
    try {
      const c = await caches.open(CACHE); const r = await c.match(path);
      if (r) return r;
    } catch (e) { /* no Cache Storage: fall through */ }
    if (path === SONGS + 'index.json') return jsonResp({ songs: [] });
    if (/\/_pack\.json$/.test(path)) return new Response('', { status: 404 });
    return origFetch(path, init);
  }
  const origFetch = window.fetch.bind(window);
  window.fetch = function (input, init) {
    try {
      const u = typeof input === 'string' || input instanceof URL ? new URL(String(input), location.href) : null;
      if (u && u.origin === location.origin && u.pathname.startsWith(SONGS)) return songFetch(u.pathname, init);
    } catch (e) { /* not ours */ }
    return origFetch(input, init);
  };

  // ---------------------------------------------------------------- .hsong reader (port of SongPacks.kt checks)
  const ID = /^[a-z0-9][a-z0-9-]{0,63}$/, SEG = /^[A-Za-z0-9_][A-Za-z0-9._-]{0,127}$/, HEX64 = /^[0-9a-f]{64}$/;
  const TAKE_FILE = /^takes\/[A-Za-z0-9_-]{1,64}\/[A-Za-z0-9_][A-Za-z0-9._-]{0,63}$/;
  const LOOKUP = 'lyrics-lookup.json', MAX_FILES = 4000, MAX_FILE_BYTES = 256 * 2 ** 20, MAX_PACK_JSON = 4 * 2 ** 20;
  const isUser = (n) => n === 'user.json' || n === LOOKUP || n.startsWith('takes/');
  const safePath = (p) => !!p && p.length <= 512 && !p.startsWith('/') && !p.includes('\\') && !p.includes(':') && p.split('/').every((s) => s !== '.' && s !== '..' && SEG.test(s));
  class Fail extends Error { constructor(code, msg) { super(msg); this.code = code; } }
  const notPack = () => new Fail('notpack', 'הקובץ הזה אינו קובץ שיר של הרמוניה (‎.hsong‎).');
  const corrupt = () => new Fail('corrupt', 'הקובץ פגום או לא שלם, לכן לא ייבאתי אותו. כדאי לשלוח או להוריד אותו שוב.');
  const unsafe = () => new Fail('unsafe', 'הקובץ מכיל נתיבים לא בטוחים, לכן לא ייבאתי אותו.');
  const u8 = async (blob) => new Uint8Array(await blob.arrayBuffer());
  const hex = (buf) => Array.from(new Uint8Array(buf), (b) => b.toString(16).padStart(2, '0')).join('');

  async function zipDir(file) { // the last end record -> the central directory (STORED entries only)
    const n = file.size; if (n < 22) throw notPack();
    const tailLen = Math.min(n, 65557), tail = await u8(file.slice(n - tailLen)), dv = new DataView(tail.buffer);
    let at = -1; for (let i = tailLen - 22; i >= 0; i--) if (dv.getUint32(i, true) === 0x06054b50) { at = i; break; }
    if (at < 0) throw notPack();
    const count = dv.getUint16(at + 10, true), cdSize = dv.getUint32(at + 12, true), cdOff = dv.getUint32(at + 16, true);
    if (cdOff + cdSize > n) throw corrupt();
    const cd = await u8(file.slice(cdOff, cdOff + cdSize)), cv = new DataView(cd.buffer), dec = new TextDecoder();
    const entries = new Map(); let p = 0;
    for (let k = 0; k < count; k++) {
      if (p + 46 > cd.length || cv.getUint32(p, true) !== 0x02014b50) throw corrupt();
      const host = cv.getUint16(p + 4, true) >> 8, method = cv.getUint16(p + 10, true), crc = cv.getUint32(p + 16, true);
      const csize = cv.getUint32(p + 20, true), usize = cv.getUint32(p + 24, true), nl = cv.getUint16(p + 28, true);
      const xl = cv.getUint16(p + 30, true), cl = cv.getUint16(p + 32, true), ext = cv.getUint32(p + 38, true), localOff = cv.getUint32(p + 42, true);
      const name = dec.decode(cd.subarray(p + 46, p + 46 + nl)); p += 46 + nl + xl + cl;
      if (method !== 0 || csize !== usize) throw corrupt();
      const mode = (ext >>> 16) & 0xF000;
      const special = name.endsWith('/') || (ext & 0x10) !== 0 || (host === 3 && (mode === 0xA000 || mode === 0x4000));
      entries.set(name, { name, localOff, size: usize, crc, special });
    }
    return entries;
  }
  async function dataOf(file, e) { // a local header's data offset
    const h = await u8(file.slice(e.localOff, e.localOff + 30)); const v = new DataView(h.buffer);
    if (h.length < 30 || v.getUint32(0, true) !== 0x04034b50) throw corrupt();
    const off = e.localOff + 30 + v.getUint16(26, true) + v.getUint16(28, true);
    if (off + e.size > file.size) throw corrupt();
    return file.slice(off, off + e.size);
  }
  const tierOf = (pk) => (!pk || pk.tier == null ? 1000 : Number.isInteger(pk.tier) && pk.tier >= 0 ? pk.tier : -1);

  async function importFile(file, progress) {
    const entries = await zipDir(file);
    const pjE = entries.get('pack.json');
    if (!pjE || pjE.localOff !== 0) throw notPack();
    if (pjE.size > MAX_PACK_JSON) throw corrupt();
    let pack; try { pack = JSON.parse(new TextDecoder().decode(await u8(await dataOf(file, pjE)))); } catch (e) { throw corrupt(); }
    if (!pack || pack.format !== 1) throw new Fail('format', 'קובץ השיר הזה בפורמט שהגרסה הזו של הרמוניה לא מכירה. כדאי לעדכן את האפליקציה.');
    if ((pack.minApp || 0) > APP_CODE) throw new Fail('newer', 'השיר הזה צריך גרסה חדשה יותר של הרמוניה. כדאי לעדכן את האפליקציה ולייבא שוב.');
    const id = String(pack.id || ''); if (!ID.test(id)) throw corrupt();
    const title = String(pack.title || '').slice(0, 200).trim() || id, artist = String(pack.artist || '').slice(0, 200);
    const arr = pack.files; if (!Array.isArray(arr) || !arr.length || arr.length > MAX_FILES) throw corrupt();
    const want = new Map();
    for (const f of arr) {
      const p = f && String(f.path || ''), b = f && f.bytes, sh = f && String(f.sha256 || '');
      if (!safePath(p)) throw unsafe();
      if (p === 'pack.json' || isUser(p) || want.has(p) || !Number.isInteger(b) || b < 0 || b > MAX_FILE_BYTES || !HEX64.test(sh)) throw corrupt();
      want.set(p, { bytes: b, sha256: sh });
    }
    if (!want.has('song.json')) throw corrupt();
    for (const e of entries.values()) {
      if (!safePath(e.name) || e.special) throw unsafe();
      if (e.name !== 'pack.json' && !want.has(e.name) && !(e.name === 'user.json' || e.name === LOOKUP || TAKE_FILE.test(e.name))) throw corrupt();
    }
    for (const [p, w] of want) { const e = entries.get(p); if (!e || e.size !== w.bytes) throw corrupt(); }
    const lib = await libRead(), old = lib.songs.find((s) => s.id === id);
    const songBytes = [...want.values()].reduce((a, w) => a + w.bytes, 0), total = songBytes * 2;
    if (pack.tier != null && old && old.audio !== false && tierOf(old.pack) >= tierOf(pack)) // (vc37 D3) never a downgrade
      return { id, title, replaced: false, unchanged: true, skipped: 'older', bytes: songBytes, files: want.size };
    if (old && old.audio !== false && old.files && Object.keys(old.files).length === want.size && [...want].every(([p, w]) => old.files[p] === w.sha256 + ':' + w.bytes))
      return { id, title, replaced: false, unchanged: true, bytes: songBytes, files: want.size };
    try { // free space (the browser's quota for this site)
      const q = await navigator.storage.estimate(); const free = (q.quota || 0) - (q.usage || 0);
      if (q.quota && free < songBytes + 32 * 2 ** 20) throw new Fail('space', 'אין מספיק מקום פנוי בטלפון לשיר הזה: צריך עוד בערך ' + Math.ceil((songBytes + 32 * 2 ** 20 - free) / 2 ** 20) + ' MB. אפשר לפנות מקום ולנסות שוב.');
    } catch (e) { if (e instanceof Fail) throw e; }
    progress(id, title, 0, total);
    // every song file checked (size + sha256) BEFORE anything is written
    let done = 0; const blobs = new Map();
    for (const [p, w] of want) {
      const blob = await dataOf(file, entries.get(p));
      if (hex(await crypto.subtle.digest('SHA-256', await blob.arrayBuffer())) !== w.sha256) throw corrupt();
      blobs.set(p, blob); done += w.bytes; progress(id, title, done, total);
    }
    const look = entries.get(LOOKUP) ? await dataOf(file, entries.get(LOOKUP)) : null; // found-by-name lyrics travel along
    const c = await caches.open(CACHE);
    try {
      // (bytes, not the picked file's lazy slices: WebKit's Cache Storage keeps them after the picker's file is gone)
      for (const [p, blob] of blobs) { await c.put(songUrl(id, p), new Response(await blob.arrayBuffer(), { headers: { 'Content-Type': typeOf(p) } })); done += blob.size; progress(id, title, done, total); }
      if (look && !want.has(LOOKUP)) await c.put(songUrl(id, LOOKUP), new Response(await look.arrayBuffer(), { headers: { 'Content-Type': 'application/json' } }));
    } catch (e) { throw new Fail('space', 'נגמר המקום בטלפון באמצע הייבוא. אפשר לפנות מקום ולנסות שוב.'); }
    if (old && old.files) for (const p of Object.keys(old.files)) if (!want.has(p)) await c.delete(songUrl(id, p)); // stale files of the old copy
    const files = {}; for (const [p, w] of want) files[p] = w.sha256 + ':' + w.bytes;
    const row = { id, title, artist, audio: true, packBytes: file.size, takeBytes: 0, files, pack: { tier: pack.tier } };
    if (pack.tier != null) row.tier = pack.tier;
    const lib2 = await libRead(); lib2.songs = lib2.songs.filter((s) => s.id !== id).concat([row]); await libWrite(lib2);
    try { if (navigator.storage && navigator.storage.persist) navigator.storage.persist(); } catch (e) { /* best effort */ }
    return { id, title, replaced: !!(old && old.audio !== false), bytes: songBytes, files: want.size, userSkipped: [...entries.keys()].some((n) => n === 'user.json' || n.startsWith('takes/')) };
  }

  // ---------------------------------------------------------------- the import status the page polls (same shape as Android)
  const BOOT = Date.now().toString(36);
  let seq = 0, status = { state: 'idle', seq: 0 }, running = false, busyOnce = false, cancelOnce = false;
  const input = document.createElement('input');
  input.type = 'file'; input.id = 'pwaFile'; input.hidden = true; // (no "accept": iOS greys out unknown extensions like .hsong)
  input.setAttribute('aria-hidden', 'true');
  const mount = () => { if (!input.isConnected) document.body.append(input); };
  if (document.body) mount(); else document.addEventListener('DOMContentLoaded', mount);
  async function runImport(file, via) {
    if (running) { busyOnce = true; return; }
    running = true; const n = ++seq, base = { seq: n, via, token: BOOT + '-' + n }, t0 = Date.now();
    status = { ...base, state: 'running', done: 0, total: -1 };
    try {
      const r = await importFile(file, (id, title, done, total) => { status = { ...base, state: 'running', id, title, done, total }; });
      status = { ...base, state: 'done', ...r, ms: Date.now() - t0 };
    } catch (e) {
      status = e instanceof Fail ? { ...base, state: 'error', code: e.code, msg: e.message, ms: Date.now() - t0 }
        : { ...base, state: 'error', code: 'io', msg: 'לא הצלחתי לקרוא או לשמור את הקובץ. כדאי לנסות שוב.', detail: String(e), ms: Date.now() - t0 };
    }
    running = false; PWA.log.push({ seq: n, state: status.state, code: status.code, id: status.id, ms: status.ms }); if (PWA.log.length > 20) PWA.log.shift();
    if (window.harmonyImportPoll) window.harmonyImportPoll();
  }
  input.addEventListener('change', () => { const f = input.files && input.files[0]; input.value = ''; if (f) runImport(f, 'pick'); else cancelOnce = true; });
  input.addEventListener('cancel', () => { cancelOnce = true; });

  // ---------------------------------------------------------------- lyrics by name (port of LyricsLookup.kt; LRCLIB, CORS *)
  const LK = { base: 'https://lrclib.net/api', client: 'harmony-lyrics/0.2 (private karaoke app; contact via github.com/fire17)', SYNCED_S: 4, PLAIN_S: 8, MAX_LINES: 400, MAX_LINE: 300, DEADLINE: 80000 };
  const lkJobs = new Map(); let lkN = 0;
  const LRC_T = /\[(\d+):(\d+(?:\.\d+)?)\]/g, TAG = /^\[[a-z]+:.*\]$/;
  function parseLrc(s) {
    const out = [];
    for (const raw of s.split(/\r\n|\r|\n/)) {
      const ts = [...raw.matchAll(LRC_T)].map((m) => +m[1] * 60 + +m[2]); const txt = raw.replace(LRC_T, '').trim();
      if (!txt || TAG.test(txt)) continue;
      if (!ts.length) out.push([null, txt]); else for (const t of ts) out.push([t, txt]);
    }
    return out.map((x, i) => [x, i]).sort((a, b) => ((a[0][0] == null) - (b[0][0] == null)) || ((a[0][0] || 0) - (b[0][0] || 0)) || (a[1] - b[1])).map((x) => x[0]);
  }
  const plain = (s) => s.split(/\r\n|\r|\n/).map((r) => r.replace(LRC_T, '').trim()).filter((t) => t && !TAG.test(t)).map((t) => [null, t]);
  function pick(rec, dur, rejected, seen) {
    if (!rec || rec.id == null) return null;
    const id = Number(rec.id); if (!(id >= 0) || seen.has(id) || rejected.has(id) || rec.instrumental) return null; seen.add(id);
    const syn = typeof rec.syncedLyrics === 'string' && rec.syncedLyrics.trim() ? rec.syncedLyrics : null;
    const pl = typeof rec.plainLyrics === 'string' && rec.plainLyrics.trim() ? rec.plainLyrics : null;
    if (!syn && !pl) return null;
    const dd = Math.abs((Number(rec.duration) || 0) - dur); let c = null;
    if (syn && dd <= LK.SYNCED_S) { const l = parseLrc(syn); c = l.some((x) => x[0] != null) ? { id, synced: true, dd, lines: l } : { id, synced: false, dd, lines: plain(pl || syn) }; }
    else if (dd <= LK.PLAIN_S) c = { id, synced: false, dd, lines: plain(pl || syn) };
    return c && c.lines.length ? c : null;
  }
  class NetFail extends Error {}
  async function lkHttp(url, t0) {
    let net = true;
    for (let k = 0; k < 3; k++) {
      if (k > 0) { if (Date.now() - t0 > LK.DEADLINE) break; await new Promise((r) => setTimeout(r, 1500 * k)); }
      let r;
      try { const ac = new AbortController(), to = setTimeout(() => ac.abort(), 18000);
        try { r = await origFetch(url, { headers: { Accept: 'application/json', 'Lrclib-Client': LK.client }, cache: 'no-store', signal: ac.signal }); } finally { clearTimeout(to); }
      } catch (e) { if (!net) throw e; continue; }
      net = false;
      if (r.status === 404) return null;
      if ([429, 500, 502, 503, 504].includes(r.status)) continue;
      if (r.status !== 200) throw new Error('http ' + r.status);
      return r.json();
    }
    if (net) throw new NetFail();
    throw new Error('busy');
  }
  async function lkRun(spec) {
    const t0 = Date.now(), { title, artist, dur } = spec, rejected = new Set(spec.rejected), q = (o) => new URLSearchParams(o).toString();
    const urls = [LK.base + '/get?' + q({ track_name: title, artist_name: artist, duration: String(Math.round(dur)) }),
      LK.base + '/search?' + q({ track_name: title, artist_name: artist }), LK.base + '/search?' + q({ track_name: title }),
      LK.base + '/search?' + q({ q: (title + ' ' + artist).trim() })];
    const seen = new Set(), out = []; let answered = false;
    for (let i = 0; i < urls.length; i++) {
      if (i >= 2 && out.length) break;
      let r; try { r = await lkHttp(urls[i], t0); answered = true; } catch (e) { if (e instanceof NetFail) continue; answered = true; continue; }
      const recs = Array.isArray(r) ? r : r && typeof r === 'object' ? [r] : [];
      for (const rec of recs) { const c = pick(rec, dur, rejected, seen); if (c) out.push(c); }
    }
    if (!answered) throw new NetFail();
    out.sort((a, b) => (a.synced ? 0 : 1) - (b.synced ? 0 : 1) || a.dd - b.dd);
    const b = out[0]; if (!b) return { state: 'done', found: false };
    return { state: 'done', found: true, synced: b.synced, providerId: b.id, durDiff: Math.round(b.dd * 10) / 10,
      lines: b.lines.slice(0, LK.MAX_LINES).map(([s, t]) => ({ t: t.slice(0, LK.MAX_LINE), s: s == null ? null : Math.round(s * 1000) / 1000 })) };
  }

  // ---------------------------------------------------------------- jobs (delete)
  const jobs = new Map(); let jobN = 0;
  async function deleteSong(id) {
    if (!ID.test(id)) return { ok: false, msg: 'bad id' };
    if (running && status.id === id) return { ok: false, msg: 'השיר הזה מיובא עכשיו.' };
    const lib = await libRead(), row = lib.songs.find((s) => s.id === id); if (!row) return { ok: false, msg: 'השיר לא נמצא.' };
    const c = await caches.open(CACHE);
    for (const p of Object.keys(row.files || {})) await c.delete(songUrl(id, p));
    await c.delete(songUrl(id, LOOKUP));
    lib.songs = lib.songs.filter((s) => s.id !== id); await libWrite(lib);
    return { ok: true, id, compacted: false, compactWhyNot: '' };
  }

  // ---------------------------------------------------------------- the bridge
  window.Android = {
    importPick() { if (running) { busyOnce = true; return; } mount(); cancelOnce = false; input.click(); },
    importStatus() {
      const o = { ...status };
      if (busyOnce) { busyOnce = false; o.busy = true; }
      if (cancelOnce) { cancelOnce = false; o.cancelled = true; }
      return JSON.stringify(o);
    },
    songDelete(id) {
      const j = 'j' + ++jobN; jobs.set(j, { state: 'running' });
      deleteSong(String(id)).then((r) => jobs.set(j, { state: 'done', ...r }), (e) => jobs.set(j, { state: 'error', ok: false, msg: 'לא הצלחתי למחוק את השיר.', detail: String(e) }));
      return j;
    },
    packJob(j) { return JSON.stringify(jobs.get(j) || { state: 'unknown' }); },
    lyricsLookup(spec) {
      let o; try { o = JSON.parse(spec); } catch (e) { return ''; }
      const title = String(o.title || '').trim().slice(0, 300), artist = String(o.artist || '').trim().slice(0, 200), dur = Number(o.dur) || 0;
      if (!title || !(dur > 0 && dur < 3600)) return '';
      const rejected = (Array.isArray(o.rejected) ? o.rejected : []).slice(0, 64).map(Number).filter((x) => x >= 0);
      const j = 'L' + ++lkN; lkJobs.set(j, { state: 'running' }); while (lkJobs.size > 16) lkJobs.delete(lkJobs.keys().next().value);
      lkRun({ title, artist, dur, rejected }).then((r) => lkJobs.set(j, r), (e) => lkJobs.set(j, { state: 'error', code: e instanceof NetFail ? 'offline' : 'net' }));
      return j;
    },
    lyricsJob(j) { return JSON.stringify(lkJobs.get(j) || { state: 'unknown' }); },
    netOnline() { return navigator.onLine !== false; },
    setState() {}, setNow() {},
  };

  // ---------------------------------------------------------------- iPhone audio
  // (1) the ring/silent switch mutes Web Audio unless the page's audio session is "playback" (Safari 17+); recording
  //     needs "play-and-record" while the mic is open, then back.
  const AS = navigator.audioSession;
  const setSession = (t) => { try { if (AS && AS.type !== t) AS.type = t; } catch (e) { /* older Safari */ } };
  setSession('playback');
  // capture: wrapped on MediaDevices.prototype (an own property on the navigator.mediaDevices instance does not stick
  // in WebKit) — "play-and-record" before the capture call, back to "playback" once every captured audio track ended.
  const MD = window.MediaDevices && window.MediaDevices.prototype, MT = window.MediaStreamTrack && window.MediaStreamTrack.prototype;
  if (MD && typeof MD.getUserMedia === 'function' && MT && typeof MT.stop === 'function') {
    const gum = MD.getUserMedia, tstop = MT.stop, live = new Set();
    const done = (t) => { if (live.delete(t) && !live.size) setSession('playback'); };
    MT.stop = function () { const r = tstop.apply(this, arguments); done(this); return r; };
    MD.getUserMedia = async function (c) {
      const mic = !!(c && c.audio); if (mic) setSession('play-and-record');
      let s; try { s = await gum.call(this, c); } catch (e) { if (mic && !live.size) setSession('playback'); throw e; }
      if (mic) {
        s.getAudioTracks().forEach((t) => { if (t.readyState === 'ended') return; live.add(t); t.addEventListener('ended', () => done(t)); });
        if (!live.size) setSession('playback');
      }
      return s;
    };
  }
  // (2) every AudioContext the page makes is listed; on the FIRST tap (touchend / click: what WebKit counts as a
  //     gesture) a context that has never run is resumed and suspended again at once, so WebKit marks it as allowed
  //     to play; the app's own play / practice taps then resume it as usual. A context the app paused (it has run)
  //     is never touched — pause / resume stays the app's (sync-exact) business.
  const AC = window.AudioContext || window.webkitAudioContext;
  const ctxs = [];
  if (AC) {
    const Wrapped = function (...a) { const c = new AC(...a); ctxs.push({ c, ran: c.state === 'running' }); c.addEventListener('statechange', () => { const x = ctxs.find((y) => y.c === c); if (x && c.state === 'running') x.ran = true; }); return c; };
    Wrapped.prototype = AC.prototype; Object.setPrototypeOf(Wrapped, AC);
    window.AudioContext = Wrapped; if (window.webkitAudioContext) window.webkitAudioContext = Wrapped;
  }
  let unlocked = false;
  const unlock = () => {
    if (unlocked) return; unlocked = true; setSession('playback');
    for (const x of ctxs) if (!x.ran && x.c.state === 'suspended') { const c = x.c; nres.call(c).then(() => { if (!x.appRan) c.suspend(); }).catch(() => {}); }
    PWA.unlockedAt = Date.now();
  };
  // the app's resume() calls mark the context as the app's from then on (so the unlock never suspends it again)
  const nres = AC && AC.prototype.resume;
  if (nres) AC.prototype.resume = function () { const x = ctxs.find((y) => y.c === this); if (x) x.appRan = true; return nres.call(this); };
  ['touchend', 'click', 'keydown'].forEach((t) => document.addEventListener(t, unlock, { capture: true, passive: true }));
  // (3) Opus: Safari decodes Ogg Opus only from iOS 18.4 (and some WebKit builds not at all). A tiny probe tells; an
  //     Ogg file this browser can't decode goes to the bundled WASM decoder instead (same AudioBuffer, same rate).
  const PROBE = 'T2dnUwACAAAAAAAAAABWAZ83AAAAAFckj+YBE09wdXNIZWFkAQI4AYC7AAAAAABPZ2dTAAAAAAAAAAAAAFYBnzcBAAAAXfpt9gE8T3B1c1RhZ3MMAAAATGF2ZjYzLjEuMTAxAQAAABwAAABlbmNvZGVyPUxhdmM2My4xLjEwMSBsaWJvcHVzT2dnUwAEeAwAAAAAAABWAZ83AgAAAI6vdZYEAwMDA/z//vz//vz//vz//g==';
  let opusNative = null; // null = not known yet, true / false = the probe's verdict
  PWA.opus = (async () => {
    try {
      const OAC = window.OfflineAudioContext || window.webkitOfflineAudioContext; if (!OAC) return (opusNative = false);
      const b = Uint8Array.from(atob(PROBE), (ch) => ch.charCodeAt(0)).buffer, o = new OAC(2, 4800, 48000);
      await new Promise((res, rej) => { const p = o.decodeAudioData(b, res, rej); if (p && p.then) p.then(res, rej); });
      return (opusNative = true);
    } catch (e) { return (opusNative = false); }
  })();
  // the fallback: vendor/ogg-opus-decoder.min.js (MIT, WASM libopus; see LICENSES.txt), loaded only when needed, one
  // decoder in a Worker (main thread if Workers fail), one file at a time -> an AudioBuffer at the context's rate
  const WD = { lib: null, dec: null, q: Promise.resolve(), n: 0 };
  const loadLib = () => WD.lib || (WD.lib = new Promise((res, rej) => {
    const s = document.createElement('script'); s.src = new URL('vendor/ogg-opus-decoder.min.js', SCOPE).href;
    s.onload = () => (window['ogg-opus-decoder'] ? res(window['ogg-opus-decoder']) : rej(new Error('no lib'))); s.onerror = () => rej(new Error('load'));
    document.head.append(s);
  }));
  async function decoder() {
    if (WD.dec) return WD.dec;
    const L = await loadLib();
    try { const d = new L.OggOpusDecoderWebWorker({ forceStereo: false }); await d.ready; WD.dec = d; WD.kind = 'worker'; }
    catch (e) { const d = new L.OggOpusDecoder({ forceStereo: false }); await d.ready; WD.dec = d; WD.kind = 'main'; }
    return WD.dec;
  }
  async function wasmDecode(ab, ctx) {
    const run = WD.q.then(async () => {
      const d = await decoder();
      const r = await d.decodeFile(new Uint8Array(ab)); await d.reset();
      if (!r || !r.samplesDecoded || !r.channelData || !r.channelData.length) throw new Error('opus: nothing decoded');
      const n = r.samplesDecoded, ch = r.channelData.length, sr = r.sampleRate || 48000;
      const OAC = window.OfflineAudioContext || window.webkitOfflineAudioContext;
      if (sr === ctx.sampleRate) { const b = ctx.createBuffer(ch, n, sr); for (let c = 0; c < ch; c++) b.getChannelData(c).set(r.channelData[c].subarray(0, n)); return b; }
      const o = new OAC(ch, Math.ceil(n * ctx.sampleRate / sr), ctx.sampleRate), src = o.createBuffer(ch, n, sr); // another rate: resampled
      for (let c = 0; c < ch; c++) src.getChannelData(c).set(r.channelData[c].subarray(0, n));
      const s = o.createBufferSource(); s.buffer = src; s.connect(o.destination); s.start();
      return o.startRendering();
    });
    WD.q = run.catch(() => {}); WD.n++;
    return run;
  }
  window.HarmonyOpusDecoder = { decode: (ab, sr, ctx) => wasmDecode(ab, ctx) };
  const BAC = window.BaseAudioContext || AC;
  if (BAC && BAC.prototype.decodeAudioData) {
    const dec = BAC.prototype.decodeAudioData;
    const isOgg = (ab) => { try { const v = new Uint8Array(ab, 0, 4); return v[0] === 0x4f && v[1] === 0x67 && v[2] === 0x67 && v[3] === 0x53; } catch (e) { return false; } };
    BAC.prototype.decodeAudioData = function (ab, ok, bad) {
      const ctx = this, ogg = ab && ab.byteLength > 4 && isOgg(ab);
      let p;
      if (ogg && opusNative === false) p = wasmDecode(ab, ctx); // this browser can't: straight to the WASM decoder
      else {
        const copy = ogg && opusNative !== true ? ab.slice(0) : null; // (decodeAudioData detaches its buffer)
        p = new Promise((res, rej) => { const q = dec.call(ctx, ab, res, rej); if (q && q.then) q.then(res, rej); })
          .catch((e) => (copy ? wasmDecode(copy, ctx) : Promise.reject(e)));
      }
      if (ok || bad) p.then(ok, bad);
      return p;
    };
  }
  PWA.wasm = WD;

  // ---------------------------------------------------------------- page bits: version line, iPhone notes, install hint
  const standalone = navigator.standalone === true || (window.matchMedia && matchMedia('(display-mode: standalone)').matches);
  const ui = () => {
    const v = document.getElementById('ver'); if (v && !/·/.test(v.textContent)) v.textContent = v.textContent + ' · ' + (IOS ? 'אייפון' : 'דפדפן') + (standalone ? ' (אפליקציה)' : '');
    const h = document.getElementById('pwaInstall');
    let seen = false; try { seen = localStorage.getItem('harmony.pwa.hint') === '1'; } catch (e) { /* noop */ }
    if (h && IOS && !standalone && !seen) { h.hidden = false; h.addEventListener('click', () => { h.hidden = true; try { localStorage.setItem('harmony.pwa.hint', '1'); } catch (e) { /* noop */ } }); }
  };
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', ui); else ui();
  // a new version: its worker takes over (skipWaiting + clients.claim in sw.js) -> this page reloads ONCE onto it,
  // unless something is playing / recording / being imported (then the next start picks it up)
  if ('serviceWorker' in navigator) {
    const hadCtrl = !!navigator.serviceWorker.controller; let reloaded = false;
    navigator.serviceWorker.addEventListener('controllerchange', () => {
      PWA.updated = Date.now(); if (!hadCtrl || reloaded) return;
      const h = window.__harmony, busy = running || (h && h.E && h.E.playing) || document.querySelector('#recBtn[aria-pressed="true"]');
      if (busy) return; reloaded = true; location.reload();
    });
    window.addEventListener('load', () => { navigator.serviceWorker.register('sw.js', { updateViaCache: 'none' }).then((r) => { PWA.sw = r.scope; r.update().catch(() => {}); }, (e) => { PWA.swError = String(e); }); });
  }

  PWA.ios = IOS; PWA.standalone = standalone; PWA.ctxs = ctxs; PWA.lib = libRead; PWA.importFile = (f) => runImport(f, 'test');
  PWA.status = () => status; PWA.lk = { lkRun, pick, parseLrc, plain }; // (tests)
  window.__harmonyPwa = PWA;
})();
