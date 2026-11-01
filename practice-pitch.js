/* Harmony live practice (v0.8.0): the pitch of the live (cleaned) mic signal, every 10 ms, in a Worker.
   The same YIN as the takes' analysis (pitch.js: 48 kHz -> 16 kHz windowed-sinc, difference function, cumulative mean
   normalisation, absolute threshold, parabolic interpolation), on the LATEST window only (live), then refined on the
   full-rate signal around the found period (16 kHz alone resolves ~1–3 cents at the top of a voice; the refinement
   resolves well under 1 cent). The window is as short as the lowest expected note allows (latency).
   In:  { port } (the worklet's blocks: { f0, d: Float32Array(256), drone }), { cfg: { fmin, fmax, gateDb } }.
   Out: { t: context frame at the window's centre, end: frame just after its last sample, cents (above 55 Hz; null =
          unvoiced), db (window level, dBFS), ap (aperiodicity at the found period: 0 = perfectly periodic, 1 = none),
          drone (Hz playing when the window ended), at: when computed (timeOrigin + now: comparable with the page's) } */
const SR = 48000, SR16 = 16000, HOP = 480, RING = 1 << 14;
let fmin = 70, fmax = 1000, gate = Math.pow(10, -60 / 20), W16 = 512;
const ring = new Float32Array(RING); let end = -1, nextAt = -1, lastDrone = 0; // end: context frame after the newest sample
const FIR = (() => { const n = 47, fc = 7200 / 48000, h = new Float32Array(n); let s = 0;
  for (let i = 0; i < n; i++) { const m = i - (n - 1) / 2, w = 0.42 - 0.5 * Math.cos(2 * Math.PI * i / (n - 1)) + 0.08 * Math.cos(4 * Math.PI * i / (n - 1));
    h[i] = (m === 0 ? 2 * fc : Math.sin(2 * Math.PI * fc * m) / (Math.PI * m)) * w; s += h[i]; }
  for (let i = 0; i < n; i++) h[i] /= s; return h; })();
const at = (f) => ring[((f % RING) + RING) % RING];
function setCfg(c) {
  if (c.fmin) fmin = c.fmin; if (c.fmax) fmax = c.fmax; if (c.gateDb != null) gate = Math.pow(10, c.gateDb / 20);
  W16 = Math.max(256, Math.min(512, Math.ceil(2.6 * SR16 / fmin)));
}
function analyse(e) { // the window ends at context frame e (exclusive)
  const TMIN = Math.max(2, Math.floor(SR16 / fmax)), TMAX = Math.ceil(SR16 / fmin), n16 = W16 + TMAX + 2, H = FIR.length, c = (H - 1) >> 1;
  const s0 = e - 3 * n16 - c; // full-rate frame of the first FIR tap needed
  if (s0 < end - RING + 8) return null;
  const x = new Float32Array(n16);
  for (let i = 0; i < n16; i++) { const o = e - 3 * (n16 - i) - c; let s = 0; for (let k = 0; k < H; k++) s += FIR[k] * at(o + k); x[i] = s; }
  // the analysis window = the LAST W16 samples (+ the lags reach back before it: the difference is taken backwards)
  const a = TMAX + 2; let en = 0; for (let i = a; i < a + W16; i++) en += x[i] * x[i];
  const rms = Math.sqrt(en / W16), db = rms > 0 ? Math.max(-120, 20 * Math.log10(rms)) : -120;
  const out = { t: e - Math.round(1.5 * W16), end: e, cents: null, db: +db.toFixed(1), ap: 1, drone: lastDrone };
  if (rms < gate) return out;
  const d = new Float32Array(TMAX + 2);
  for (let t = 1; t <= TMAX + 1; t++) { let s = 0; for (let i = a; i < a + W16; i++) { const v = x[i] - x[i - t]; s += v * v; } d[t] = s; }
  let run = 0; for (let t = 1; t <= TMAX + 1; t++) { run += d[t]; d[t] = run > 0 ? d[t] * t / run : 1; }
  let tau = -1; for (let t = TMIN; t <= TMAX; t++) { if (d[t] < 0.15) { while (t + 1 <= TMAX && d[t + 1] < d[t]) t++; tau = t; break; } }
  if (tau < 0) { let m = 1; for (let t = TMIN; t <= TMAX; t++) m = Math.min(m, d[t]); out.ap = +m.toFixed(3); return out; }
  out.ap = +d[tau].toFixed(3);
  if (d[tau] >= 0.3) return out;
  const y0 = d[tau - 1], y1 = d[tau], y2 = d[tau + 1], den = y0 - 2 * y1 + y2, t16 = den !== 0 ? tau + 0.5 * (y0 - y2) / den : tau;
  // refine at 48 kHz: the plain difference function around 3 * t16 over the same span, parabola through the minimum
  const W48 = 3 * W16, T0 = Math.round(3 * t16), dd = new Float64Array(9);
  for (let k = 0; k < 9; k++) { const T = T0 - 4 + k; let s = 0; for (let i = e - W48; i < e; i++) { const v = at(i) - at(i - T); s += v * v; } dd[k] = s; }
  let k = 1; for (let j = 2; j < 8; j++) if (dd[j] < dd[k]) k = j;
  const z0 = dd[k - 1], z1 = dd[k], z2 = dd[k + 1], dz = z0 - 2 * z1 + z2, T48 = T0 - 4 + k + (dz > 0 ? 0.5 * (z0 - z2) / dz : 0);
  const f = SR / (Math.abs(T48 - 3 * t16) < 2 ? T48 : 3 * t16);
  out.cents = +(1200 * Math.log2(f / 55)).toFixed(2);
  return out;
}
let inPort = null;
function onBlock(m) {
  const f0 = m.f0, d = m.d, n = d.length;
  if (end >= 0 && f0 !== end) { /* a gap (dropped input): the ring simply continues at the new frame */ }
  for (let i = 0; i < n; i++) ring[((f0 + i) % RING + RING) % RING] = d[i];
  end = f0 + n; lastDrone = m.drone || 0;
  if (nextAt < 0 || nextAt > end + 4 * HOP) nextAt = end;
  while (nextAt <= end) { const r = analyse(nextAt); if (r) { r.at = performance.timeOrigin + performance.now(); postMessage(r); } nextAt += HOP; }
}
onmessage = (e) => {
  const m = e.data || {};
  if (m.port) { if (inPort) inPort.close(); inPort = m.port; end = -1; nextAt = -1; inPort.onmessage = (ev) => onBlock(ev.data); } // (a new node: the screen reopened)
  if (m.cfg) setCfg(m.cfg);
  if (m.test) { postMessage({ test: analyseBuffer(m.test) }); } // (tests: the same analysis on a given buffer)
};
function analyseBuffer(t) { // { d: Float32Array at 48 kHz, cfg } -> the last window's result
  if (t.cfg) setCfg(t.cfg); const d = t.d; for (let i = 0; i < d.length; i++) ring[i % RING] = d[i]; end = d.length; return analyse(end);
}
setCfg({});
