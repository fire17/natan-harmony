/* Harmony pitch view (v0.4.8): the take's pitch vs the song's own vocal melody, per sung line.
   - track(): YIN on the take, 48 kHz -> 16 kHz, one value per 10 ms song frame (frame j is centred on song time
     j * 10 ms, the same grid as the reference melody: pyin, frame 1024, hop 160, centred).
   - compare(): per line of the song package (its phrases), the same method as the offline analysis: voiced take
     frames within ±300 ms of the line vs confident reference frames inside it, DTW on octave-folded cents (timing
     removed per line), deviation in cents along the path.
   Runs as a Worker (messages below) and as a plain script / Node module (tests). No DOM, no network. */
(function (root) {
  const HOP = 0.01, SR16 = 16000, HOP16 = 160, W = 512, TMIN = Math.floor(SR16 / 900), TMAX = Math.ceil(SR16 / 65);
  const NONE = -32768;

  // 48 kHz -> 16 kHz: windowed-sinc low-pass (cut-off 7.2 kHz, 47 taps), every 3rd sample
  const FIR = (() => { const n = 47, fc = 7200 / 48000, h = new Float32Array(n); let s = 0;
    for (let i = 0; i < n; i++) { const m = i - (n - 1) / 2, w = 0.42 - 0.5 * Math.cos(2 * Math.PI * i / (n - 1)) + 0.08 * Math.cos(4 * Math.PI * i / (n - 1));
      h[i] = (m === 0 ? 2 * fc : Math.sin(2 * Math.PI * fc * m) / (Math.PI * m)) * w; s += h[i]; }
    for (let i = 0; i < n; i++) h[i] /= s; return h; })();
  function down3(x) { // x: Float32Array at 48 kHz (song frames from 0) -> 16 kHz, sample i = song frame 3i
    const n = Math.floor(x.length / 3), y = new Float32Array(n), H = FIR.length, c = (H - 1) >> 1;
    for (let i = 0; i < n; i++) { const o = 3 * i - c; let s = 0;
      if (o >= 0 && o + H <= x.length) { for (let k = 0; k < H; k++) s += FIR[k] * x[o + k]; }
      else { for (let k = 0; k < H; k++) { const j = o + k; if (j >= 0 && j < x.length) s += FIR[k] * x[j]; } }
      y[i] = s; }
    return y;
  }

  // YIN (de Cheveigné & Kawahara 2002): difference function over a 512-sample window (32 ms, as pyin's), cumulative
  // mean normalisation, absolute threshold, parabolic interpolation. Returns cents above 55 Hz per 10 ms frame (NaN =
  // unvoiced) for song frames [f0, f1). Silent frames (< -50 dBFS RMS) are skipped (cheap).
  function track(x16, f0, f1, opt) { return trackOffset(x16, 0, f0, f1, opt); }

  // the take (Int16 chunks on the song timeline, chunk k = song frames [kC, (k+1)C)) -> pitch per 10 ms frame
  // (v0.7.0) straight from the Int16 chunks to 16 kHz: no full-rate copy of the take (a 4-min take was 50 MB of Float32
  // before the low-pass); the same taps, the same order, the same values (d * 2^-15 is exact) -> the same result as before
  function trackTake(chunks, C, startF, endF, opt) {
    const a = Math.max(0, startF - 4000), b = endF + 4000, A0 = a - (a % 3); // 16 kHz sample i = song frame A0 + 3i
    const n16 = Math.floor((b - A0) / 3), x16 = new Float32Array(n16), H = FIR.length, c = (H - 1) >> 1, INV = 1 / 32768, M = new Map();
    for (const [k, d] of chunks) M.set(k, d);
    const sig = (f) => { if (f < startF || f >= endF) return 0; const k = Math.floor(f / C), d = M.get(k); return d && f - k * C < d.length ? d[f - k * C] * INV : 0; };
    for (let i = 0; i < n16; i++) {
      const o = A0 + 3 * i - c, k = Math.floor(o / C), d = M.get(k), off = o - k * C; let s = 0;
      if (d && off + H <= d.length && o >= startF && o + H <= endF) { for (let q = 0; q < H; q++) s += FIR[q] * (d[off + q] * INV); }
      else { for (let q = 0; q < H; q++) s += FIR[q] * sig(o + q); }
      x16[i] = s;
    }
    const s16 = A0 / 3; // song frame 3*(s16 + i)
    const f0 = Math.ceil(startF / 480), f1 = Math.floor(endF / 480), db = new Float32Array(Math.max(0, f1 - f0)).fill(-120);
    return { f0, cents: tidy(trackOffset(x16, s16, f0, f1, opt, db), opt), db }; // (v0.7.0) db: the frame's level, dBFS (raw take)
  }
  // pyin smooths its track with an HMM; the same spirit, cheaply: voiced runs shorter than minRun frames are dropped
  // (blips), and each voiced run gets a 7-frame running median (single-frame octave / outlier jumps)
  function tidy(c, opt) {
    const minRun = opt && opt.minRun != null ? opt.minRun : 8, mw = opt && opt.median != null ? opt.median : 7, h = mw >> 1, out = c.slice(), trim = (opt && opt.trim) || 0;
    let i = 0;
    while (i < c.length) {
      if (isNaN(c[i])) { i++; continue; }
      let j = i; while (j < c.length && !isNaN(c[j])) j++;
      if (j - i < minRun) { for (let k = i; k < j; k++) out[k] = NaN; }
      else {
        if (mw > 1) { for (let k = i; k < j; k++) { const w = []; for (let q = Math.max(i, k - h); q <= Math.min(j - 1, k + h); q++) w.push(c[q]); w.sort((x, y) => x - y); out[k] = w[w.length >> 1]; } }
        for (let k = 0; k < trim; k++) { out[i + k] = NaN; out[j - 1 - k] = NaN; } // onset / release glides
      }
      i = j;
    }
    return out;
  }
  function trackOffset(x16, s16, f0, f1, opt, db) { // like track(), but x16[0] is 16 kHz sample s16 of the song; db: optional level out
    const th = (opt && opt.threshold) || 0.12, gate = Math.pow(10, ((opt && opt.gateDb) || -50) / 20), vth = (opt && opt.voicing) || th;
    const out = new Float32Array(Math.max(0, f1 - f0)).fill(NaN), d = new Float32Array(TMAX + 2);
    for (let j = f0; j < f1; j++) {
      const a = j * HOP16 - (W >> 1) - s16;
      if (a < 0 || a + W + TMAX + 1 > x16.length) continue;
      let e = 0; for (let i = a; i < a + W; i++) e += x16[i] * x16[i];
      if (db) db[j - f0] = e > 0 ? Math.max(-120, 10 * Math.log10(e / W)) : -120;
      if (Math.sqrt(e / W) < gate) continue;
      for (let t = 1; t <= TMAX + 1; t++) { let s = 0; for (let i = a; i < a + W; i++) { const v = x16[i] - x16[i + t]; s += v * v; } d[t] = s; }
      let run = 0;
      for (let t = 1; t <= TMAX + 1; t++) { run += d[t]; d[t] = run > 0 ? d[t] * t / run : 1; }
      let tau = -1;
      for (let t = TMIN; t <= TMAX; t++) { if (d[t] < th) { while (t + 1 <= TMAX && d[t + 1] < d[t]) t++; tau = t; break; } }
      if (tau < 0 || d[tau] >= vth) continue; // voiced only when clearly periodic (pyin calls breathy / gliding frames unvoiced)
      const y0 = d[tau - 1], y1 = d[tau], y2 = d[tau + 1], den = y0 - 2 * y1 + y2;
      const tt = den !== 0 ? tau + 0.5 * (y0 - y2) / den : tau;
      out[j - f0] = 1200 * Math.log2(SR16 / tt / 55);
    }
    return out;
  }

  // melody.json -> { cents: Float32Array (NaN = unvoiced), conf: Float32Array 0..1 }
  function b64(s) { if (typeof atob === 'function') { const b = atob(s), u = new Uint8Array(b.length); for (let i = 0; i < b.length; i++) u[i] = b.charCodeAt(i); return u; } return new Uint8Array(Buffer.from(s, 'base64')); }
  function melody(j) {
    const cb = b64(j.cents), cf = b64(j.conf), n = j.frames, dv = new DataView(cb.buffer, cb.byteOffset, cb.byteLength);
    const cents = new Float32Array(n), conf = new Float32Array(n);
    for (let i = 0; i < n; i++) { const v = dv.getInt16(2 * i, true); cents[i] = v === NONE ? NaN : v; conf[i] = cf[i] / 255; }
    return { cents, conf, minConf: j.minConf || 0.6 };
  }

  const med = (a) => { if (!a.length) return NaN; const s = Float64Array.from(a).sort(), n = s.length; return n % 2 ? s[n >> 1] : (s[n / 2 - 1] + s[n / 2]) / 2; };
  const fold = (c) => { const v = ((c + 600) % 1200 + 1200) % 1200; return v - 600; };
  // per line: DTW of the take's voiced frames (line ±300 ms) against the confident reference frames of the line
  function compare(take, ref, phrases, opt) { // take: { f0, cents }, ref: melody(), phrases: [{ t0, t1 }]; opt.pairs: keep each line's path as [ref frame, take frame] (v0.7.0)
    const nf = Math.min(ref.cents.length, take.f0 + take.cents.length);
    const ct = (i) => { const k = i - take.f0; return k >= 0 && k < take.cents.length ? take.cents[k] : NaN; };
    const lines = [], dots = []; // dots: [frame, cents deviation or NaN (= grey: no reliable reference), line]
    phrases.forEach((q, li) => {
      const r0 = Math.floor(q.t0 / HOP), r1 = Math.min(nf, Math.floor(q.t1 / HOP) + 1), t0 = Math.max(0, r0 - 30), t1 = Math.min(nf, r1 + 30);
      const ri = [], ti = [];
      for (let i = r0; i < r1; i++) if (!isNaN(ref.cents[i]) && ref.conf[i] >= ref.minConf) ri.push(i);
      for (let i = t0; i < t1; i++) if (!isNaN(ct(i))) ti.push(i);
      const rec = { line: li + 1, t0: q.t0, t1: q.t1, ref: ri.length, take: ti.length, ok: false };
      if (ri.length < 15 || ti.length < 15) { ti.forEach((i) => dots.push([i, NaN, li])); lines.push(rec); return; }
      const N = ri.length, M = ti.length, D = new Float64Array(N * M);
      const cost = (a, b) => { const x = Math.min(Math.abs(fold(ref.cents[ri[a]] - ct(ti[b]))), 300) / 300, td = Math.abs(ri[a] - ti[b]) * HOP; return x + (td > 0.35 ? 5 : td * 0.5); };
      for (let a = 0; a < N; a++) for (let b = 0; b < M; b++) {
        const c = cost(a, b); let m;
        if (a === 0 && b === 0) m = 0; else { m = Infinity; if (a > 0 && b > 0) m = D[(a - 1) * M + b - 1]; if (b > 0 && D[a * M + b - 1] < m) m = D[a * M + b - 1]; if (a > 0 && D[(a - 1) * M + b] < m) m = D[(a - 1) * M + b]; }
        D[a * M + b] = c + m;
      }
      const path = []; let a = N - 1, b = M - 1; path.push([a, b]);
      while (a > 0 || b > 0) { // librosa's order on ties: diagonal, then (0, 1), then (1, 0)
        if (a === 0) b--; else if (b === 0) a--;
        else { const dg = D[(a - 1) * M + b - 1], l = D[a * M + b - 1], u = D[(a - 1) * M + b]; if (dg <= l && dg <= u) { a--; b--; } else if (l <= u) b--; else a--; }
        path.push([a, b]);
      }
      path.reverse();
      const lag = [], cents = [], dev = new Map();
      for (const [x, y] of path) { lag.push((ti[y] - ri[x]) * HOP * 1000); const c = fold(ct(ti[y]) - ref.cents[ri[x]]); cents.push(c); dev.set(ti[y], [c, Math.abs(ti[y] - ri[x]) * HOP]); }
      dev.forEach(([c, dt], i) => dots.push([i, dt > 0.2 ? NaN : c, li])); // aligned far away in time: no honest reference -> grey
      const pc = (c) => ((Math.round(c / 100) % 12) + 12) % 12;
      let same = 0; for (const [x, y] of path) if (pc(ct(ti[y])) === pc(ref.cents[ri[x]])) same++;
      Object.assign(rec, { ok: true, lagMs: Math.round(med(lag)), centsMedian: Math.round(med(cents)), centsMeanAbs: Math.round(cents.reduce((p, c) => p + Math.abs(c), 0) / cents.length),
        pctBeyond50: Math.round(100 * cents.filter((c) => Math.abs(c) > 50).length / cents.length), sameNotePct: Math.round(100 * same / path.length), path: path.length });
      if (opt && opt.pairs) rec.pairs = path.map(([x, y]) => [ri[x], ti[y]]);
      lines.push(rec);
    });
    const seen = new Set(dots.map((d) => d[0])); // voiced take frames outside every line (a bridge, an ad-lib): no reference -> grey
    for (let i = take.f0; i < take.f0 + take.cents.length; i++) if (!seen.has(i) && !isNaN(ct(i))) dots.push([i, NaN, -1]);
    dots.sort((p, q) => p[0] - q[0]);
    return { lines, dots };
  }

  const API = { HOP, down3, track, trackTake, melody, compare, fold, med };
  if (typeof module !== 'undefined' && module.exports) module.exports = API;
  else root.HarmonyPitch = API;
  // Worker: { id, chunks: [[k, Int16Array]], C, startF, endF } -> { id, f0, cents (Float32Array), db (Float32Array), ms }
  //         { id, op: 'voice', inp } -> { id, res } (HarmonyVoice.analyse, when voice.js is loaded into the same Worker)
  if (typeof WorkerGlobalScope !== 'undefined' && root instanceof WorkerGlobalScope) {
    root.onmessage = (e) => { const m = e.data, t = Date.now();
      try {
        if (m.op === 'voice') { const r = root.HarmonyVoice.analyse(m.inp); root.postMessage({ id: m.id, res: r, ms: Date.now() - t }); return; } // (v0.7.0) voice.js, same Worker
        const r = trackTake(m.chunks, m.C, m.startF, m.endF); root.postMessage({ id: m.id, f0: r.f0, cents: r.cents, db: r.db, ms: Date.now() - t }, [r.cents.buffer, r.db.buffer]); }
      catch (err) { root.postMessage({ id: m.id, error: String(err) }); } };
  }
})(typeof self !== 'undefined' ? self : this);
