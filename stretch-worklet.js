/* Harmony tempo: pitch-preserving tempo change for the summed stem bus.
   The stems play at playbackRate r (song tempo × r, pitch × r); this processor shifts the pitch back by p = 1 / r
   without changing duration: WSOLA time-stretch by p (waveform-similarity overlap-add on 60 ms sequences, 8 ms
   crossfades, best splice searched over 20 ms by cross-correlation) followed by a cubic (Catmull-Rom) resampler
   that reads the stretched stream p frames per output frame. One instance per song (on the mix bus, after the
   per-stem gains), stereo, a few µs per 128-frame block. Message {p} sets the factor and resets the state.
   Delay: the splice offsets depend on the music, so the delay is not a constant of p. Every sequence knows exactly
   where its centre input frame lands in the output (output frame = m0 + stretched index / p, m0 = output frame where
   reading began), so the processor reports {latency} once per reset: the mean over its first 16 splices (~0.6 s).
   v0.5.3: the message may carry gen (echoed in every report, so the page ignores an earlier run's numbers), and every
   ~1 s it also reports {latAll, n}: the mean over ALL splices since the reset (a recording uses the take's own mean). */
const SEQ = 2880, OVL = 384, SEEK = 960, RING = 1 << 16, MASK = RING - 1;

class HarmonyStretch extends AudioWorkletProcessor {
  constructor() {
    super();
    this.inL = new Float32Array(RING); this.inR = new Float32Array(RING);
    this.stL = new Float32Array(RING); this.stR = new Float32Array(RING);
    this.ovL = new Float32Array(OVL); this.ovR = new Float32Array(OVL);
    this.p = 1; this.reset();
    this.gen = null;
    this.port.onmessage = (e) => { if (e.data && e.data.p > 0) { this.p = e.data.p; this.gen = e.data.gen != null ? e.data.gen : null; this.reset(); } };
  }
  reset() {
    this.inW = 0; this.ip = 0; this.stW = 0; this.rp = 0; this.started = false; this.first = true;
    this.outN = 0; this.m0 = 0; this.pend = []; this.lat = 0; this.latN = 0; this.sent = false; this.all = 0; this.allN = 0; this.lastRep = 0;
    this.inL.fill(0); this.inR.fill(0); this.ovL.fill(0); this.ovR.fill(0);
  }
  // offset in [0, SEEK) where the input best continues the previous sequence's tail (mono, coarse then fine)
  bestOffset(base) {
    const iL = this.inL, iR = this.inR, oL = this.ovL, oR = this.ovR;
    const corr = (d, step) => {
      let s = 0, e = 0;
      for (let i = 0; i < OVL; i += step) {
        const k = (base + d + i) & MASK, x = iL[k] + iR[k];
        s += x * (oL[i] + oR[i]); e += x * x;
      }
      return s / Math.sqrt(e + 1e-9);
    };
    let best = 0, bv = -Infinity;
    for (let d = 0; d < SEEK; d += 8) { const v = corr(d, 4); if (v > bv) { bv = v; best = d; } }
    const c = best;
    for (let d = Math.max(0, c - 7); d <= Math.min(SEEK - 1, c + 7); d++) { const v = corr(d, 1); if (v > bv) { bv = v; best = d; } }
    return best;
  }
  sequence() { // one WSOLA step: SEQ - OVL stretched frames out, input advances (SEQ - OVL) / p
    const base = Math.floor(this.ip);
    const d = this.first ? 0 : this.bestOffset(base);
    this.pend.push([this.stW + SEQ / 2, base + d + SEQ / 2]); // (stretched index, input frame) of this sequence's centre
    const iL = this.inL, iR = this.inR, sL = this.stL, sR = this.stR;
    let w = this.stW;
    for (let i = 0; i < OVL; i++, w++) {
      const k = (base + d + i) & MASK, a = i / OVL;
      sL[w & MASK] = this.first ? iL[k] : this.ovL[i] * (1 - a) + iL[k] * a;
      sR[w & MASK] = this.first ? iR[k] : this.ovR[i] * (1 - a) + iR[k] * a;
    }
    for (let i = OVL; i < SEQ - OVL; i++, w++) { const k = (base + d + i) & MASK; sL[w & MASK] = iL[k]; sR[w & MASK] = iR[k]; }
    for (let i = 0; i < OVL; i++) { const k = (base + d + SEQ - OVL + i) & MASK; this.ovL[i] = iL[k]; this.ovR[i] = iR[k]; }
    this.stW = w; this.ip += (SEQ - OVL) / this.p; this.first = false;
  }
  process(inputs, outputs) {
    const inp = inputs[0], out = outputs[0], n = out[0].length;
    const xL = inp[0], xR = inp[1] || inp[0];
    for (let i = 0; i < n; i++) {
      const k = (this.inW + i) & MASK;
      this.inL[k] = xL ? xL[i] : 0; this.inR[k] = xR ? xR[i] : 0;
    }
    this.inW += n;
    const need = () => this.rp + n * this.p + 4;
    while (this.stW < need() + (this.started ? 0 : SEQ) && Math.floor(this.ip) + SEEK + SEQ <= this.inW) this.sequence();
    const yL = out[0], yR = out[1] || out[0];
    if (!this.started && this.stW >= need() + SEQ - OVL) { this.started = true; this.m0 = this.outN; } // margin, then run
    if (!this.started) { yL.fill(0); if (yR !== yL) yR.fill(0); this.outN += n; return true; }
    for (const [sIdx, inFrame] of this.pend) { // exact delay of each sequence centre (input frame -> output frame)
      const L = this.m0 + sIdx / this.p - inFrame;
      if (this.latN < 16) { this.latN++; this.lat += (L - this.lat) / this.latN; }   // mean of the first 16 splices
      if (this.latN === 16 && !this.sent) { this.sent = true; this.port.postMessage({ latency: this.lat, gen: this.gen }); } // once
      this.allN++; this.all += (L - this.all) / this.allN;
    }
    if (this.allN && this.outN - this.lastRep >= sampleRate) { this.lastRep = this.outN; this.port.postMessage({ latAll: this.all, n: this.allN, gen: this.gen }); }
    this.pend.length = 0;
    const sL = this.stL, sR = this.stR;
    for (let i = 0; i < n; i++) {
      const j = Math.floor(this.rp), f = this.rp - j;
      const a = (j - 1) & MASK, b = j & MASK, c = (j + 1) & MASK, e = (j + 2) & MASK;
      const cr = (y0, y1, y2, y3) => y1 + 0.5 * f * (y2 - y0 + f * (2 * y0 - 5 * y1 + 4 * y2 - y3 + f * (3 * (y1 - y2) + y3 - y0)));
      yL[i] = cr(sL[a], sL[b], sL[c], sL[e]);
      if (yR !== yL) yR[i] = cr(sR[a], sR[b], sR[c], sR[e]);
      this.rp += this.p;
    }
    this.outN += n;
    return true;
  }
}
registerProcessor('harmony-stretch', HarmonyStretch);

/* Harmony key change (v0.5.3): phase-vocoder pitch shift with a CONSTANT delay (2048 frames), duration unchanged.
   Why not the WSOLA above: a splice + resampler moves each transient by a different amount (measured at +2 semitones:
   recorded clicks −12…+6 ms around the mean), so a take recorded in a transposed key could not be placed within 2 ms.
   Here every analysis frame is resynthesised at its own position: STFT 2048 / hop 512 (Hann, 75 % overlap); per frame
   the spectral peaks of the mid channel (L + R) are found, each peak's region of bins moves to round(k·p) and is rotated
   by one phase (identity phase locking, Laroche & Dolson): the partial's phase runs at its true frequency × p, the bins
   around it keep their phase relations (no phasiness), left / right keep their phase differences (the stereo image).
   Message {p, gen}: factor (pitch × p) and reset; it reports {latency: 2048, gen} at once and {latAll, n} once a second. */
const PVN = 2048, PVH = 512, PVK = PVN / 2 + 1;
class HarmonyPV extends AudioWorkletProcessor {
  constructor() {
    super();
    this.win = new Float32Array(PVN); for (let i = 0; i < PVN; i++) this.win[i] = 0.5 - 0.5 * Math.cos(2 * Math.PI * i / PVN);
    this.re = new Float64Array(PVN); this.im = new Float64Array(PVN); this.yre = new Float64Array(PVN); this.yim = new Float64Array(PVN);
    this.inL = new Float32Array(PVN); this.inR = new Float32Array(PVN); this.outL = new Float32Array(PVN * 2); this.outR = new Float32Array(PVN * 2);
    this.phA = new Float64Array(PVK); this.phS = new Float64Array(PVK); this.mag = new Float64Array(PVK); this.pm = new Float64Array(PVK);
    this.peaks = new Int32Array(PVK); this.tw = makeTw(PVN); this.br = makeBr(PVN);
    this.p = 1; this.gen = null; this.reset();
    this.port.onmessage = (e) => { if (e.data && e.data.p > 0) { this.p = e.data.p; this.gen = e.data.gen != null ? e.data.gen : null; this.reset(); this.port.postMessage({ latency: PVN, gen: this.gen }); } };
  }
  reset() { this.inL.fill(0); this.inR.fill(0); this.outL.fill(0); this.outR.fill(0); this.phA.fill(0); this.phS.fill(0); this.cnt = 0; this.wpos = 0; this.rpos = 0; this.n = 0; this.lastRep = 0; this.first = true; }
  frame() { // the last PVN input samples (ring, oldest at wpos) -> shifted, windowed, added to the output accumulator
    const N = PVN, K = PVK, re = this.re, im = this.im, w = this.win, p = this.p;
    for (let i = 0; i < N; i++) { const j = (this.wpos + i) % N; re[i] = this.inL[j] * w[i]; im[i] = this.inR[j] * w[i]; } // L + i·R in one FFT
    fftC(re, im, this.tw, this.br, false);
    // unpack: XL[k] = (Z[k] + conj Z[N−k]) / 2, XR[k] = (Z[k] − conj Z[N−k]) / 2i ; mid = (XL + XR) / 2
    const XLr = this.yre, XLi = this.yim, XRr = this.XRr || (this.XRr = new Float64Array(K)), XRi = this.XRi || (this.XRi = new Float64Array(K));
    for (let k = 0; k < K; k++) { const a = re[k], b = im[k], c = re[(N - k) % N], d = -im[(N - k) % N];
      XLr[k] = 0.5 * (a + c); XLi[k] = 0.5 * (b + d); XRr[k] = 0.5 * (b - d); XRi[k] = -0.5 * (a - c); }
    const mag = this.mag, pm = this.pm, phA = this.phA, phS = this.phS, H = PVH;
    let mx = 0;
    for (let k = 0; k < K; k++) { const mr = XLr[k] + XRr[k], mi = XLi[k] + XRi[k]; mag[k] = mr * mr + mi * mi; pm[k] = Math.atan2(mi, mr); if (mag[k] > mx) mx = mag[k]; }
    // peaks of the mid magnitude
    let np = 0; const thr = mx * 1e-9;
    for (let k = 1; k < K - 1; k++) if (mag[k] > thr && mag[k] > mag[k - 1] && mag[k] >= mag[k + 1]) this.peaks[np++] = k;
    const Yr = this.oLr || (this.oLr = new Float64Array(K)), Yi = this.oLi || (this.oLi = new Float64Array(K)), Zr = this.oRr || (this.oRr = new Float64Array(K)), Zi = this.oRi || (this.oRi = new Float64Array(K));
    Yr.fill(0); Yi.fill(0); Zr.fill(0); Zi.fill(0);
    const nps = this.nps || (this.nps = new Float64Array(K)); nps.fill(0); const wrote = this.wrote || (this.wrote = new Uint8Array(K)); wrote.fill(0);
    for (let q = 0; q < np; q++) {
      const kp = this.peaks[q], lo = q ? ((this.peaks[q - 1] + kp) >> 1) + 1 : 0, hi = q + 1 < np ? (kp + this.peaks[q + 1]) >> 1 : K - 1;
      const omega = 2 * Math.PI * kp / N; let dp = pm[kp] - phA[kp] - H * omega; dp -= 2 * Math.PI * Math.round(dp / (2 * Math.PI));
      const f = omega + dp / H, jp = Math.round(kp * p), sh = jp - kp;
      if (jp <= 0 || jp >= K - 1) continue;
      const psi = this.first ? pm[kp] : phS[jp] + H * f * p, rot = psi - pm[kp], cr = Math.cos(rot), ci = Math.sin(rot);
      for (let k = lo; k <= hi; k++) { const j = k + sh; if (j < 0 || j >= K) continue;
        Yr[j] += XLr[k] * cr - XLi[k] * ci; Yi[j] += XLr[k] * ci + XLi[k] * cr; Zr[j] += XRr[k] * cr - XRi[k] * ci; Zi[j] += XRr[k] * ci + XRi[k] * cr;
        nps[j] = pm[k] + rot; wrote[j] = 1; }
    }
    for (let k = 0; k < K; k++) { phA[k] = pm[k]; if (wrote[k]) phS[k] = nps[k]; }
    this.first = false;
    // back: z = yL + i·yR from the two spectra (Hermitian halves), one inverse FFT
    for (let k = 0; k < N; k++) { let a, b, c, d; if (k < K) { a = Yr[k]; b = Yi[k]; c = Zr[k]; d = Zi[k]; } else { const m = N - k; a = Yr[m]; b = -Yi[m]; c = Zr[m]; d = -Zi[m]; }
      re[k] = a - d; im[k] = b + c; }
    fftC(re, im, this.tw, this.br, true);
    const g = 1 / 1.5; // Hann² at 75 % overlap sums to 1.5
    for (let i = 0; i < N; i++) { const j = (this.opos + i) % (2 * N); this.outL[j] += re[i] * w[i] * g; this.outR[j] += im[i] * w[i] * g; }
  }
  process(inputs, outputs) {
    const inp = inputs[0], out = outputs[0], n = out[0].length, xL = inp[0], xR = inp[1] || inp[0], yL = out[0], yR = out[1] || out[0], N = PVN;
    for (let i = 0; i < n; i++) {
      this.inL[this.wpos] = xL ? xL[i] : 0; this.inR[this.wpos] = xR ? xR[i] : 0; this.wpos = (this.wpos + 1) % N;
      // output: the sample written N frames ago (frames add to [t − N, t); it is final when t has moved N on)
      const j = this.rpos; yL[i] = this.outL[j]; if (yR !== yL) yR[i] = this.outR[j]; this.outL[j] = 0; this.outR[j] = 0; this.rpos = (this.rpos + 1) % (2 * N);
      if (++this.cnt === PVH) { this.cnt = 0; this.opos = (this.rpos + N - PVN + 2 * N) % (2 * N); this.frame(); }
    }
    this.n += n;
    if (this.n - this.lastRep >= sampleRate) { this.lastRep = this.n; this.port.postMessage({ latAll: PVN, n: 1, gen: this.gen }); }
    return true;
  }
}
function makeTw(N) { const t = new Float64Array(N); for (let i = 0; i < N / 2; i++) { t[2 * i] = Math.cos(2 * Math.PI * i / N); t[2 * i + 1] = -Math.sin(2 * Math.PI * i / N); } return t; }
function makeBr(N) { const b = new Uint32Array(N), L = Math.log2(N); for (let i = 0; i < N; i++) { let r = 0, x = i; for (let k = 0; k < L; k++) { r = (r << 1) | (x & 1); x >>= 1; } b[i] = r; } return b; }
function fftC(re, im, tw, br, inv) { // in place, radix 2; inverse scaled 1/N
  const N = re.length;
  for (let i = 0; i < N; i++) { const j = br[i]; if (j > i) { let t = re[i]; re[i] = re[j]; re[j] = t; t = im[i]; im[i] = im[j]; im[j] = t; } }
  for (let s = 2; s <= N; s <<= 1) { const h = s >> 1, st = N / s;
    for (let i = 0; i < N; i += s) for (let k = 0; k < h; k++) { const wr = tw[2 * k * st], wi = inv ? -tw[2 * k * st + 1] : tw[2 * k * st + 1], a = i + k, b = a + h;
      const xr = re[b] * wr - im[b] * wi, xi = re[b] * wi + im[b] * wr; re[b] = re[a] - xr; im[b] = im[a] - xi; re[a] += xr; im[a] += xi; } }
  if (inv) for (let i = 0; i < N; i++) { re[i] /= N; im[i] /= N; }
}
registerProcessor('harmony-pv', HarmonyPV);
