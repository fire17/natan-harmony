/* Harmony speaker-mode cleaning (v0.5.0): remove the song the phone itself played from a speaker-mode take.
   The reference is EXACT: the app's own output (what went to the speaker), tapped during the recording on the same
   audio clock and stored with the take. Steps, all offline after the take stops:
     1. alignment: GCC-PHAT between reference and take over the loud parts (search −20 … +120 ms), median of windows;
     2. removal: partitioned-block frequency-domain adaptive filter (overlap-save, block 512 @ 48 kHz, 15 partitions =
        160 ms of room), normalised per bin, one partition gradient-constrained per block (rotating, as Speex MDF);
        pass 1 learns the room over the whole take; pass 2 starts from it and adapts slowly only where he is NOT
        singing (a near-end mask from pass 1), so his voice never trains the filter (double-talk safeguard);
     3. a gentle residual suppressor: per bin, Wiener-like gain from the remaining echo estimate, floor −12 dB,
        smoothed over time — tuned to keep the voice natural rather than to remove the last dB.
   The raw take is never touched: the result is a separate, derived track. Runs as a Worker or a Node module. */
(function (root) {
  const B = 512, M = 2 * B, K = B + 1;

  // ---- radix-2 complex FFT (in place, interleaved re/im), sizes powers of two
  const fftCache = new Map();
  function plan(n) {
    let p = fftCache.get(n); if (p) return p;
    const rev = new Uint32Array(n), cos = new Float64Array(n / 2), sin = new Float64Array(n / 2), bits = Math.log2(n);
    for (let i = 0; i < n; i++) { let r = 0; for (let b = 0; b < bits; b++) r |= ((i >> b) & 1) << (bits - 1 - b); rev[i] = r; }
    for (let i = 0; i < n / 2; i++) { cos[i] = Math.cos(2 * Math.PI * i / n); sin[i] = -Math.sin(2 * Math.PI * i / n); }
    p = { rev, cos, sin }; fftCache.set(n, p); return p;
  }
  function fft(re, im, inv) {
    const n = re.length, { rev, cos, sin } = plan(n);
    for (let i = 0; i < n; i++) { const j = rev[i]; if (j > i) { let t = re[i]; re[i] = re[j]; re[j] = t; t = im[i]; im[i] = im[j]; im[j] = t; } }
    for (let size = 2; size <= n; size <<= 1) {
      const h = size >> 1, step = n / size;
      for (let s = 0; s < n; s += size) for (let k = 0; k < h; k++) {
        const wr = cos[k * step], wi = inv ? -sin[k * step] : sin[k * step], a = s + k, b = a + h;
        const xr = re[b] * wr - im[b] * wi, xi = re[b] * wi + im[b] * wr;
        re[b] = re[a] - xr; im[b] = im[a] - xi; re[a] += xr; im[a] += xi;
      }
    }
    if (inv) for (let i = 0; i < n; i++) { re[i] /= n; im[i] /= n; }
  }
  // real signal of length M -> K = M/2+1 bins (re, im arrays of length K), via one complex FFT of length M
  const R1 = new Float64Array(M), I1 = new Float64Array(M);
  function rfft(x, outR, outI) { R1.set(x); I1.fill(0); fft(R1, I1, false); for (let k = 0; k < K; k++) { outR[k] = R1[k]; outI[k] = I1[k]; } }
  function irfft(inR, inI, out) { // K bins -> M real samples
    for (let k = 0; k < K; k++) { R1[k] = inR[k]; I1[k] = inI[k]; }
    for (let k = K; k < M; k++) { R1[k] = inR[M - k]; I1[k] = -inI[M - k]; }
    fft(R1, I1, true); for (let i = 0; i < M; i++) out[i] = R1[i];
  }

  // ---- 1. delay of the take behind the reference (frames), GCC-PHAT on up to 12 loud 4 s windows
  function align(x, y, sr) {
    const N = 1 << 17, lo = -Math.round(0.02 * sr), hi = Math.round(0.12 * sr), win = Math.min(N / 2, Math.round(4 * sr));
    const cand = []; for (let s = 0; s + win <= Math.min(x.length, y.length); s += win) { let e = 0; for (let i = s; i < s + win; i += 8) e += x[i] * x[i]; cand.push([e, s]); }
    cand.sort((a, b) => b[0] - a[0]);
    const lags = [];
    for (const [, s] of cand.slice(0, 12)) {
      const xr = new Float64Array(N), xi = new Float64Array(N), yr = new Float64Array(N), yi = new Float64Array(N);
      for (let i = 0; i < win; i++) { xr[i] = x[s + i]; yr[i] = y[s + i]; }
      fft(xr, xi, false); fft(yr, yi, false);
      for (let k = 0; k < N; k++) { const r = yr[k] * xr[k] + yi[k] * xi[k], i = yi[k] * xr[k] - yr[k] * xi[k], m = Math.hypot(r, i) + 1e-12; xr[k] = r / m; xi[k] = i / m; }
      fft(xr, xi, true);
      let best = -Infinity, at = 0; for (let l = lo; l <= hi; l++) { const v = xr[(l + N) % N]; if (v > best) { best = v; at = l; } }
      lags.push(at);
    }
    lags.sort((a, b) => a - b);
    return { lag: lags.length ? lags[lags.length >> 1] : 0, lags };
  }

  // ---- 2. PBFDAF; returns echo estimate (time) and error; W can be given (warm start) and is returned
  function pbfdaf(x, y, P, opt) {
    // (v0.5.2) x may be an array of channels (stereo reference): one filter per channel, all adapted from the same error,
    // the step normalised by the summed reference power (multichannel NLMS); one channel = exactly the v0.5.1 filter
    const XC = Array.isArray(x) ? x : [x], ch = XC.length;
    const n = Math.floor(Math.min(XC[0].length, y.length) / B) * B, nb = n / B;
    const mk = () => Array.from({ length: P }, () => new Float64Array(K));
    const WRc = opt.W ? opt.W.rc : Array.from({ length: ch }, mk), WIc = opt.W ? opt.W.ic : Array.from({ length: ch }, mk);
    const XRc = Array.from({ length: ch }, mk), XIc = Array.from({ length: ch }, mk);
    const S = new Float64Array(K).fill(1e-6), buf = new Float64Array(M), tr = new Float64Array(M), Er = new Float64Array(K), Ei = new Float64Array(K), Yr = new Float64Array(K), Yi = new Float64Array(K);
    const eo = opt.energyOnly, yh = eo ? null : new Float32Array(n), e = eo ? null : new Float32Array(n), mu = opt.mu, near = opt.near, onProg = opt.onProg;
    const bE = new Float64Array(nb), bY = new Float64Array(nb), eb = new Float64Array(B); // per-block energies (pass 1 keeps only these)
    let head = 0;
    for (let b = 0; b < nb; b++) {
      head = (head + P - 1) % P; // newest spectrum goes to Xr[head]; partition p uses X[(head + p) % P]
      for (let c = 0; c < ch; c++) { const xx = XC[c]; for (let i = 0; i < B; i++) { buf[i] = b ? xx[(b - 1) * B + i] : 0; buf[B + i] = xx[b * B + i]; } rfft(buf, XRc[c][head], XIc[c][head]); }
      Yr.fill(0); Yi.fill(0);
      for (let c = 0; c < ch; c++) { const Xr = XRc[c], Xi = XIc[c], Wr = WRc[c], Wi = WIc[c];
        for (let p = 0; p < P; p++) { const q = (head + p) % P, ar = Xr[q], ai = Xi[q], wr = Wr[p], wi = Wi[p]; for (let k = 0; k < K; k++) { Yr[k] += ar[k] * wr[k] - ai[k] * wi[k]; Yi[k] += ar[k] * wi[k] + ai[k] * wr[k]; } } }
      irfft(Yr, Yi, tr);
      { let se = 0, sy = 0; for (let i = 0; i < B; i++) { const v = tr[B + i], r = y[b * B + i] - v; eb[i] = r; se += r * r; sy += v * v; if (!eo) { yh[b * B + i] = v; e[b * B + i] = r; } } bE[b] = se; bY[b] = sy; }
      const m = typeof mu === 'number' ? mu : mu(b, near ? near[b] : 0);
      if (ch === 1) { const xr0 = XRc[0][head], xi0 = XIc[0][head]; for (let k = 0; k < K; k++) S[k] = 0.9 * S[k] + 0.1 * (xr0[k] * xr0[k] + xi0[k] * xi0[k]); } // every block (never stale)
      else for (let k = 0; k < K; k++) { let pw = 0; for (let c = 0; c < ch; c++) { const a = XRc[c][head][k], d = XIc[c][head][k]; pw += a * a + d * d; } S[k] = 0.9 * S[k] + 0.1 * pw; }
      if (m > 0) {
        for (let i = 0; i < B; i++) { buf[i] = 0; buf[B + i] = eb[i]; }
        rfft(buf, Er, Ei);
        let floor = 0; for (let k = 0; k < K; k++) floor += S[k]; floor = floor / K * (opt.reg || 0.02) + 1e-10; // quiet bins must not get huge steps
        for (let c = 0; c < ch; c++) { const Xr = XRc[c], Xi = XIc[c], Wr = WRc[c], Wi = WIc[c];
          for (let p = 0; p < P; p++) { const q = (head + p) % P, ar = Xr[q], ai = Xi[q], wr = Wr[p], wi = Wi[p];
            for (let k = 0; k < K; k++) { const g = m / (P * S[k] + floor); wr[k] += g * (ar[k] * Er[k] + ai[k] * Ei[k]); wi[k] += g * (ar[k] * Ei[k] - ai[k] * Er[k]); } }
          const p = b % P; // rotating gradient constraint: partition p back to a causal B-tap filter
          irfft(Wr[p], Wi[p], tr); for (let i = B; i < M; i++) tr[i] = 0; rfft(tr, Wr[p], Wi[p]); }
      }
      if (onProg && (b & 255) === 0) onProg(b / nb);
    }
    return { yh, e, bE, bY, W: { rc: WRc, ic: WIc, r: WRc[0], i: WIc[0] }, n };
  }

  // ---- 3. residual suppressor (STFT 1024 / hop 256, sqrt-Hann): gain from the remaining echo estimate
  function suppress(e, yh, leak, opt) {
    const N = 1024, H = 256, Kb = N / 2 + 1, n = e.length, w = new Float64Array(N);
    for (let i = 0; i < N; i++) w[i] = Math.sqrt(0.5 - 0.5 * Math.cos(2 * Math.PI * i / N));
    const out = new Float32Array(n), er = new Float64Array(N), ei = new Float64Array(N), yr = new Float64Array(N), yi = new Float64Array(N), G = new Float64Array(Kb).fill(1);
    const extra = opt.extra || [], xo = extra.map(() => new Float32Array(n)), zr = new Float64Array(N), zi = new Float64Array(N); // (tests) the same gains on components
    const floor = opt.floor, over = opt.over;
    // (v0.5.1) residual echo from the REFERENCE'S POWER: on a real phone part of the echo follows the music's spectrum but
    // not its waveform (speaker DSP, two speakers, movement) — no linear estimate captures it. Its power per band is
    // learnt where only the song plays: c(band, segment) = Σ|E|² / Σ P_ref, P_ref = Σ channels |X|² held with a 100 ms
    // decay (the room's tail); smoothed across 1 s segments (forward-backward, τ 5 s). Echo power = max(linear, c·P_ref).
    const res = opt.res || null, NQ = 33, rr = new Float64Array(N), ri = new Float64Array(N), Ps = new Float64Array(Kb);
    let cS = null, segOf = null, nseg = 0;
    const refPow = (s) => { // P_ref of the frame starting at s (held), into Ps
      const dec = Math.exp(-H / (res.sr * 0.1)); const cur = new Float64Array(Kb);
      for (const x of res.xc) { for (let i = 0; i < N; i++) { const j = s + i; rr[i] = j >= 0 && j < x.length ? x[j] * w[i] : 0; ri[i] = 0; } fft(rr, ri, false); for (let k = 0; k < Kb; k++) cur[k] += rr[k] * rr[k] + ri[k] * ri[k]; }
      for (let k = 0; k < Kb; k++) Ps[k] = Math.max(cur[k], Ps[k] * dec); };
    if (res) {
      const seg = res.sr; nseg = Math.ceil(n / seg) + 1; segOf = (s) => Math.max(0, Math.min(nseg - 1, Math.floor((s + N / 2) / seg)));
      const num = new Float64Array(nseg * NQ), den = new Float64Array(nseg * NQ);
      for (let s = -N + H; s < n; s += H) { refPow(s); if (!res.songOnly(s + N / 2)) continue;
        for (let i = 0; i < N; i++) { const j = s + i; er[i] = j >= 0 && j < n ? e[j] * w[i] : 0; ei[i] = 0; } fft(er, ei, false);
        const o = segOf(s) * NQ; for (let k = 0; k < Kb; k++) { const q = Math.min(NQ - 1, k >> 4); num[o + q] += er[k] * er[k] + ei[k] * ei[k]; den[o + q] += Ps[k]; } }
      const a = Math.exp(-1 / (res.tau || 5)), fbS = (S) => { const acc = new Float64Array(NQ), F = new Float64Array(S.length);
        for (let g = 0; g < nseg; g++) for (let q = 0; q < NQ; q++) { acc[q] = a * acc[q] + S[g * NQ + q]; F[g * NQ + q] = acc[q]; }
        acc.fill(0); for (let g = nseg - 1; g >= 0; g--) for (let q = 0; q < NQ; q++) { acc[q] = a * acc[q] + S[g * NQ + q]; F[g * NQ + q] += acc[q] - S[g * NQ + q]; } return F; };
      const nS = fbS(num), dS = fbS(den); cS = new Float64Array(nseg * NQ); for (let i = 0; i < cS.length; i++) cS[i] = dS[i] > 0 ? (res.scale || 1) * nS[i] / dS[i] : 0;
      Ps.fill(0);
    }
    for (let s = -N + H; s < n; s += H) {
      if (res) refPow(s);
      for (let i = 0; i < N; i++) { const j = s + i, ok = j >= 0 && j < n; er[i] = ok ? e[j] * w[i] : 0; ei[i] = 0; yr[i] = ok ? yh[j] * w[i] : 0; yi[i] = 0; }
      fft(er, ei, false); fft(yr, yi, false);
      for (let k = 0; k < Kb; k++) {
        const pe = er[k] * er[k] + ei[k] * ei[k]; let pr = (yr[k] * yr[k] + yi[k] * yi[k]) * leak[Math.min(leak.length - 1, k >> 4)];
        if (res) pr = Math.max(pr, cS[segOf(s) * NQ + Math.min(NQ - 1, k >> 4)] * Ps[k]);
        const g = Math.max(floor, 1 - over * pr / (pe + 1e-12));
        G[k] = g < G[k] ? 0.6 * G[k] + 0.4 * g : 0.3 * G[k] + 0.7 * g; // fast to open (voice), a little slower to close
        er[k] *= G[k]; ei[k] *= G[k]; if (k > 0 && k < N / 2) { er[N - k] *= G[k]; ei[N - k] *= G[k]; }
      }
      fft(er, ei, true);
      for (let i = 0; i < N; i++) { const j = s + i; if (j >= 0 && j < n) out[j] += er[i] * w[i] * (2 * H / N); }
      extra.forEach((sig, q) => { for (let i = 0; i < N; i++) { const j = s + i; zr[i] = j >= 0 && j < n ? sig[j] * w[i] : 0; zi[i] = 0; } fft(zr, zi, false);
        for (let k = 0; k < Kb; k++) { zr[k] *= G[k]; zi[k] *= G[k]; if (k > 0 && k < N / 2) { zr[N - k] *= G[k]; zi[N - k] *= G[k]; } } fft(zr, zi, true);
        for (let i = 0; i < N; i++) { const j = s + i; if (j >= 0 && j < n) xo[q][j] += zr[i] * w[i] * (2 * H / N); } });
    }
    if (extra.length) out.extra = xo;
    return out;
  }

  // ---- the whole pass: x = reference (what the phone played), y = the take, same song frames
  function clean(x, y, sr, opt) {
    opt = opt || {}; const prog = opt.onProg || (() => {}), P = opt.partitions || 15, t0 = Date.now();
    // stereo reference (opt.xR = the right channel, x = the left): the room filter and the alignment use the mono mix
    // (memory) the Worker passes its message as opt.src: the inputs are taken from it and released once copied (shifted)
    if (opt.src) { x = opt.src.x; opt.xR = opt.src.xR || null; opt.src.x = opt.src.xR = null; }
    let xR = opt.xR && opt.xR.length ? opt.xR : null, xL = x; opt.xR = null;
    if (xR) { const m = new Float32Array(Math.min(xL.length, xR.length)); for (let i = 0; i < m.length; i++) m[i] = 0.5 * (xL[i] + xR[i]); x = m; }
    const al = align(x, y, sr), d = al.lag;
    const sh = (v) => { const o = new Float32Array(y.length); for (let i = 0; i < y.length; i++) { const j = i - d; o[i] = j >= 0 && j < v.length ? v[j] : 0; } return o; };
    const xs = sh(x), xc = xR ? [sh(xL), sh(xR)] : [xs]; const stereo = !!xR;
    x = xL = xR = null; // (released: only the aligned copies are used from here)
    // before any filter: the echo coupling (mic power / reference power) is stable for a phone lying still; the
    // quietest 20 % of blocks are song-only -> their ratio is the coupling; a block > 6 dB above it has him singing
    const nb0 = Math.floor(Math.min(xs.length, y.length) / B), r0 = [], pxB = new Float64Array(nb0), pyB = new Float64Array(nb0);
    let pxSum = 0; for (let b = 0; b < nb0; b++) { let a = 0, c = 0; for (let i = b * B; i < (b + 1) * B; i++) { a += xs[i] * xs[i]; c += y[i] * y[i]; } pxB[b] = a; pyB[b] = c; pxSum += a; }
    const pxMean = pxSum / nb0; for (let b = 0; b < nb0; b++) if (pxB[b] > pxMean * 0.05) r0.push(pyB[b] / pxB[b]);
    r0.sort((a, b) => a - b); const g2 = r0.length ? r0[Math.floor(r0.length * 0.2)] : 1;
    const clipB = new Uint8Array(nb0); if (opt.clipAware !== false) for (let b = 0; b < nb0; b++) for (let i = b * B; i < (b + 1) * B; i++) if (y[i] >= 0.999 || y[i] <= -0.999) { clipB[b] = 1; break; }
    const dtk = opt.dtk || 3, wid = opt.widen != null ? opt.widen : 4, raw0 = new Uint8Array(nb0), near0 = new Uint8Array(nb0);
    for (let b = 0; b < nb0; b++) raw0[b] = pyB[b] > dtk * g2 * pxB[b] + 1e-9 * B || clipB[b] ? 1 : 0; // clipped input: never adapt on it
    for (let b = 0; b < nb0; b++) if (raw0[b]) for (let q = Math.max(0, b - wid); q <= Math.min(nb0 - 1, b + wid); q++) near0[q] = 1; // his notes' edges too
    // pass 1: learn the room only where the song alone is heard
    const mu1 = opt.mu1 || 0.3, p1 = pbfdaf(stereo ? xc : xs, y, P, { mu: (b, nr) => (nr ? 0 : mu1), near: near0, energyOnly: true, onProg: (f) => prog(0.05 + 0.4 * f) });
    const nb = p1.n / B, near = new Uint8Array(nb), refOn = new Uint8Array(nb);
    let xe = 0; for (let i = 0; i < p1.n; i++) xe += xs[i] * xs[i]; const xMean = xe / p1.n;
    for (let b = 0; b < nb; b++) { const pe = p1.bE[b], py = p1.bY[b], px = pxB[b];
      refOn[b] = px > xMean * 0.01 ? 1 : 0; near[b] = (pe > 2 * py + 1e-7 * B) || near0[b] ? 1 : 0; }
    // widen the near-end mask by ±3 blocks (onsets / tails of his notes)
    const nearW = new Uint8Array(nb); for (let b = 0; b < nb; b++) if (near[b]) for (let q = Math.max(0, b - 3); q <= Math.min(nb - 1, b + 3); q++) nearW[q] = 1;
    // pass 2: from the learnt room, slow adaptation only while he is silent
    const muS = opt.muSing || 0, p2 = pbfdaf(stereo ? xc : xs, y, P, { W: p1.W, mu: (b, nr) => (nr ? (clipB[b] ? 0 : muS) : 0.12), near: nearW, onProg: (f) => prog(0.45 + 0.4 * f) });
    // v2 (v0.5.1): a second, TIME-VARYING linear estimate in the STFT domain, the better one per frame, a guard, the
    // gentle suppressor (see stft2() below)
    const r2 = stft2(xs, y, p2.yh, p2.n, sr, g2, opt, (f) => prog(0.85 + 0.08 * f), xc);
    // leakage per 16-bin band: residual / echo estimate where only the song plays (where it is reliable)
    const NB = 33, num = new Float64Array(NB), den = new Float64Array(NB), Nf = 1024, w = new Float64Array(Nf);
    for (let i = 0; i < Nf; i++) w[i] = 0.5 - 0.5 * Math.cos(2 * Math.PI * i / Nf);
    const ar = new Float64Array(Nf), ai = new Float64Array(Nf), br = new Float64Array(Nf), bi = new Float64Array(Nf);
    let used = 0;
    for (let b = 0; b + 2 < nb && used < 4000; b += 2) { if (nearW[b] || nearW[b + 1] || !refOn[b] || clipB[b]) continue; const s = b * B;
      for (let i = 0; i < Nf; i++) { ar[i] = r2.e[s + i] * w[i]; ai[i] = 0; br[i] = r2.yh[s + i] * w[i]; bi[i] = 0; }
      fft(ar, ai, false); fft(br, bi, false);
      for (let k = 0; k <= Nf / 2; k++) { const q = Math.min(NB - 1, k >> 4); num[q] += ar[k] * ar[k] + ai[k] * ai[k]; den[q] += br[k] * br[k] + bi[k] * bi[k]; } used++; }
    const leak = new Float64Array(NB); for (let q = 0; q < NB; q++) leak[q] = den[q] > 0 ? Math.min(1, num[q] / den[q]) : 0.1;
    prog(0.94);
    // (tests) components through the same processing: the echo left after the linear stage, and the voice
    const extra = opt.components ? [Float32Array.from(r2.e, (v, i) => opt.components.echo[i] - r2.yh[i]), opt.components.voice.subarray(0, r2.n)] : [];
    const resM = opt.resPow ? { xc, sr, tau: opt.resTau || 5, scale: opt.resScale || 1, songOnly: (i) => { const b = Math.floor(i / B); return b >= 0 && b < nb && !nearW[b] && refOn[b] && !clipB[b]; } } : null;
    const sup = suppress(r2.e, r2.yh, leak, { floor: opt.floor != null ? opt.floor : 0.35, over: opt.over != null ? opt.over : 1.0, extra, res: resM });
    const o = new Float32Array(y.length); o.set(sup.subarray(0, Math.min(sup.length, y.length))); for (let i = sup.length; i < y.length; i++) o[i] = y[i];
    let my = 0, mo = 0, nOnly = 0;
    for (let b = 0; b < nb; b++) { if (nearW[b] || !refOn[b] || clipB[b]) continue; let a = 0, c = 0; for (let i = b * B; i < (b + 1) * B; i++) { a += y[i] * y[i]; c += o[i] * o[i]; } my += a; mo += c; nOnly++; }
    prog(1);
    const stats = { v: 2, alignMs: +(d * 1000 / sr).toFixed(2), alignSpreadMs: al.lags.length ? +((al.lags[al.lags.length - 1] - al.lags[0]) * 1000 / sr).toFixed(2) : null,
      reductionDb: my > 0 && mo > 0 ? +(10 * Math.log10(my / mo)).toFixed(1) : null, linearErleDb: r2.erle, songOnlySec: +(nOnly * B / sr).toFixed(1),
      singingSec: +(nearW.reduce((p, v) => p + v, 0) * B / sr).toFixed(1), clippedSec: +(clipB.reduce((p, v) => p + v, 0) * B / sr).toFixed(1),
      guardedSec: r2.guardedSec, refChannels: r2.channels, roomFilterPct: r2.roomPct, trackingPct: +(100 - r2.roomPct).toFixed(1), partitions: P, tailMs: Math.round(P * B * 1000 / sr), ms: Date.now() - t0 };
    return { out: o, stats, masks: { near: nearW, refOn }, filt: { lag: d, leak }, comp: sup.extra || null };
  }

  // ---- real FFT of length N via one complex FFT of N/2 (packing + post-processing)
  function rfftPlan(N) {
    const h = N / 2, cr = new Float64Array(h), ci = new Float64Array(h), wr = new Float64Array(h), wi = new Float64Array(h);
    for (let k = 0; k < h; k++) { wr[k] = Math.cos(2 * Math.PI * k / N); wi[k] = -Math.sin(2 * Math.PI * k / N); }
    return {
      fwd(x, oR, oI) { // x: N reals -> bins 0..N/2
        for (let i = 0; i < h; i++) { cr[i] = x[2 * i]; ci[i] = x[2 * i + 1]; }
        fft(cr, ci, false);
        for (let k = 0; k <= h; k++) { const a = k % h, b = (h - k) % h, er = 0.5 * (cr[a] + cr[b]), ei = 0.5 * (ci[a] - ci[b]), or_ = 0.5 * (ci[a] + ci[b]), oi = -0.5 * (cr[a] - cr[b]);
          const tr = k < h ? wr[k] : -1, ti = k < h ? wi[k] : 0; oR[k] = er + (or_ * tr - oi * ti); oI[k] = ei + (or_ * ti + oi * tr); }
      },
      inv(iR, iI, x) { // bins 0..N/2 -> N reals
        for (let k = 0; k < h; k++) { const ar = iR[k], ai = iI[k], br = iR[h - k], bi = -iI[h - k];
          const er = 0.5 * (ar + br), ei = 0.5 * (ai + bi), dr = 0.5 * (ar - br), di = 0.5 * (ai - bi), tr = wr[k], ti = -wi[k];
          const or_ = dr * tr - di * ti, oi = dr * ti + di * tr; cr[k] = er - oi; ci[k] = ei + or_; }
        fft(cr, ci, true); for (let i = 0; i < h; i++) { x[2 * i] = cr[i]; x[2 * i + 1] = ci[i]; }
      },
    };
  }

  // ---- v2 STFT stage (N 4096 / hop 2048, sqrt-Hann): a time-varying Wiener echo estimate H(f, t) from cross / auto
  // spectra over song-only frames, per 1 s segment, smoothed forward AND backward in time (τ 5 s: follows a phone that
  // moves); per frame the echo estimate (this one or the room filter's yh) that leaves LESS energy is used (a linear
  // echo estimate cannot remove his voice, so less residual = less echo); a frame where even that would be louder than
  // the mic keeps the mic (guard: never worse than the raw take); then gain = max(floor, 1 − over·L·|Ŷ|²/|E|²).
  function stft2(xs, y, yh, n, sr, g2, opt, prog, xc) {
    xc = xc || [xs];
    const N = 4096, H = 2048, K = N / 2 + 1, nf = Math.max(0, Math.floor((n - N) / H) + 1), R = rfftPlan(N);
    const w = new Float64Array(N); for (let i = 0; i < N; i++) w[i] = Math.sqrt(0.5 - 0.5 * Math.cos(2 * Math.PI * i / N));
    const fr = new Float64Array(N), Xr = new Float64Array(K), Xi = new Float64Array(K), Yr = new Float64Array(K), Yi = new Float64Array(K), Ar = new Float64Array(K), Ai = new Float64Array(K);
    const spec = (sig, t, oR, oI) => { const s0 = t * H; for (let i = 0; i < N; i++) fr[i] = sig[s0 + i] * w[i]; R.fwd(fr, oR, oI); };
    // frame energies (time domain, windowed) + clipping -> first song-only guess from the echo coupling
    const px = new Float64Array(nf), py = new Float64Array(nf), clip = new Uint8Array(nf);
    for (let t = 0; t < nf; t++) { let a = 0, b = 0, c = 0; const s0 = t * H; for (let i = 0; i < N; i++) { const ww = w[i] * w[i], xv = xs[s0 + i], yv = y[s0 + i]; a += xv * xv * ww; b += yv * yv * ww; if (yv >= 0.999 || yv <= -0.999) c = 1; } px[t] = a; py[t] = b; clip[t] = c; }
    let pm = 0; for (let t = 0; t < nf; t++) pm += px[t]; pm /= Math.max(1, nf);
    const act = (t) => px[t] > pm * 0.02, kappa = opt.kappa || 2;
    const so0 = new Uint8Array(nf); for (let t = 0; t < nf; t++) so0[t] = act(t) && !clip[t] && py[t] < kappa * 1.5 * g2 * px[t] ? 1 : 0;
    // per 1 s segment over song-only frames: cross spectra reference -> mic and the reference's own (auto / cross between
    // channels). (v0.5.1) STEREO: the phone plays left and right through two speakers at different distances from the mic
    // — one filter on the mono mix can't model that (measured on real takes: the delay jumps between 150 / 159 / 166
    // samples as the mix moves between the channels); with both channels it is a 2-input Wiener filter per bin.
    const fps = Math.max(1, Math.round(sr / H)), ns = Math.ceil(nf / fps), ch = xc.length, M = ns * K;
    const Z = () => new Float64Array(M);
    const S1r = Z(), S1i = Z(), S11 = Z(), S2r = ch > 1 ? Z() : null, S2i = ch > 1 ? Z() : null, S22 = ch > 1 ? Z() : null, S12r = ch > 1 ? Z() : null, S12i = ch > 1 ? Z() : null;
    const X2r = new Float64Array(K), X2i = new Float64Array(K);
    // (his voice is uncorrelated with the reference: frames where he sings add variance, not bias — they count with a
    // smaller weight, so the path is still followed through long sung passages)
    const wSing = opt.wSing != null ? opt.wSing : 0;
    for (let t = 0; t < nf; t++) { const wt = so0[t] ? 1 : act(t) && !clip[t] ? wSing : 0; if (!wt) continue; spec(xc[0], t, Xr, Xi); spec(y, t, Yr, Yi); if (ch > 1) spec(xc[1], t, X2r, X2i); const o = Math.floor(t / fps) * K;
      for (let k = 0; k < K; k++) { const j = o + k; S1r[j] += wt * (Xr[k] * Yr[k] + Xi[k] * Yi[k]); S1i[j] += wt * (Xr[k] * Yi[k] - Xi[k] * Yr[k]); S11[j] += wt * (Xr[k] * Xr[k] + Xi[k] * Xi[k]);
        if (ch > 1) { S2r[j] += wt * (X2r[k] * Yr[k] + X2i[k] * Yi[k]); S2i[j] += wt * (X2r[k] * Yi[k] - X2i[k] * Yr[k]); S22[j] += wt * (X2r[k] * X2r[k] + X2i[k] * X2i[k]);
          S12r[j] += wt * (Xr[k] * X2r[k] + Xi[k] * X2i[k]); S12i[j] += wt * (Xr[k] * X2i[k] - Xi[k] * X2r[k]); } } // conj(X1)·X2
      if ((t & 63) === 0) prog(0.3 * t / nf); }
    // forward-backward exponential smoothing across segments (in place: F + B − own)
    const a = Math.exp(-1 / ((opt.tau || (ch > 1 ? 3 : 5)) * sr / (fps * H))); // (stereo: τ 3 s — the two-speaker path moves faster with the mix)
    const fb = (S) => { if (!S) return; const acc = new Float64Array(K), F = new Float64Array(M);
      for (let q = 0; q < ns; q++) { const o = q * K; for (let k = 0; k < K; k++) { acc[k] = a * acc[k] + S[o + k]; F[o + k] = acc[k]; } }
      acc.fill(0); for (let q = ns - 1; q >= 0; q--) { const o = q * K; for (let k = 0; k < K; k++) { acc[k] = a * acc[k] + S[o + k]; F[o + k] += acc[k] - S[o + k]; } }
      S.set(F); };
    let mx = 0; for (let i = 0; i < M; i++) mx += S11[i] + (ch > 1 ? S22[i] : 0); const reg = 1e-3 * mx / Math.max(1, M * ch) + 1e-12; // (from the raw sums, as v0.5.1-mono)
    [S1r, S1i, S11, S2r, S2i, S22, S12r, S12i].forEach(fb);
    const H1r = Z(), H1i = Z(), H2r = ch > 1 ? Z() : null, H2i = ch > 1 ? Z() : null;
    for (let j = 0; j < M; j++) {
      if (ch === 1) { H1r[j] = S1r[j] / (S11[j] + reg); H1i[j] = S1i[j] / (S11[j] + reg); continue; }
      // [S11 S12; conj(S12) S22] [h1; h2] = [S1; S2]
      const A = S11[j] + reg, D = S22[j] + reg, br = S12r[j], bi = S12i[j], det = A * D - (br * br + bi * bi);
      const p1r = S1r[j] * D - (br * S2r[j] - bi * S2i[j]), p1i = S1i[j] * D - (br * S2i[j] + bi * S2r[j]);
      const p2r = A * S2r[j] - (br * S1r[j] + bi * S1i[j]), p2i = A * S2i[j] - (br * S1i[j] - bi * S1r[j]);
      H1r[j] = p1r / det; H1i[j] = p1i / det; H2r[j] = p2r / det; H2i[j] = p2i / det;
    }
    // the time-varying echo estimate of frame t -> (Wr, Wi)
    const est = (t, Wr, Wi) => { const o = Math.floor(t / fps) * K; spec(xc[0], t, Xr, Xi); if (ch > 1) spec(xc[1], t, X2r, X2i);
      for (let k = 0; k < K; k++) { const j = o + k; let wr = Xr[k] * H1r[j] - Xi[k] * H1i[j], wi = Xr[k] * H1i[j] + Xi[k] * H1r[j];
        if (ch > 1) { wr += X2r[k] * H2r[j] - X2i[k] * H2i[j]; wi += X2r[k] * H2i[j] + X2i[k] * H2r[j]; } Wr[k] = wr; Wi[k] = wi; } };
    const Wr = new Float64Array(K), Wi = new Float64Array(K);
    // pass B: residual energy of both estimates per frame
    const e1 = new Float64Array(nf), e2 = new Float64Array(nf), pyF = new Float64Array(nf); // (spectral energies: same scale as e1 / e2)
    for (let t = 0; t < nf; t++) {
      est(t, Wr, Wi); spec(y, t, Yr, Yi); spec(yh, t, Ar, Ai);
      let s1 = 0, s2 = 0, sy = 0;
      for (let k = 0; k < K; k++) { const wr = Wr[k], wi = Wi[k];
        const r1 = Yr[k] - wr, i1 = Yi[k] - wi, r2 = Yr[k] - Ar[k], i2 = Yi[k] - Ai[k]; s1 += r1 * r1 + i1 * i1; s2 += r2 * r2 + i2 * i2; sy += Yr[k] * Yr[k] + Yi[k] * Yi[k]; }
      e1[t] = s1; e2[t] = s2; pyF[t] = sy;
      if ((t & 63) === 0) prog(0.3 + 0.35 * t / nf);
    }
    // choice per frame (residual smoothed over 3 frames) + guard
    const use1 = new Uint8Array(nf), guard = new Uint8Array(nf); let nRoom = 0, nGuard = 0;
    // (margins: where his voice dominates both residuals are ~equal and the difference is noise — keep the room filter;
    // the guard needs the residual clearly louder than the mic, 1 dB over 3 frames)
    const mW = opt.wienerMargin || 0.8, mG = opt.guardMargin || 1.26;
    for (let t = 0; t < nf; t++) { let a1 = 0, a2 = 0, ay = 0; for (let u = Math.max(0, t - 1); u <= Math.min(nf - 1, t + 1); u++) { a1 += e1[u]; a2 += e2[u]; ay += pyF[u]; }
      use1[t] = a1 < mW * a2 ? 1 : 0; if (!use1[t]) nRoom++;
      if ((use1[t] ? a1 : a2) > mG * ay) { guard[t] = 1; nGuard++; } }
    // pass C: the chosen linear residual E and echo estimate Ŷ back to the time domain (the suppressor follows in clean())
    const e = new Float32Array(n), yo = new Float32Array(n), ob = new Float64Array(N), Er = new Float64Array(K), Ei = new Float64Array(K);
    const erleA = new Float64Array(8), erleB = new Float64Array(8);
    for (let t = 0; t < nf; t++) {
      if (use1[t] && !guard[t]) est(t, Wr, Wi); spec(y, t, Yr, Yi); spec(yh, t, Ar, Ai); const g = guard[t], u1 = use1[t];
      let se = 0;
      for (let k = 0; k < K; k++) {
        let hr = 0, hi = 0; if (!g) { if (u1) { hr = Wr[k]; hi = Wi[k]; } else { hr = Ar[k]; hi = Ai[k]; } }
        Er[k] = Yr[k] - hr; Ei[k] = Yi[k] - hi; se += Er[k] * Er[k] + Ei[k] * Ei[k]; Ar[k] = hr; Ai[k] = hi;
      }
      if (so0[t]) { const q = Math.min(7, Math.floor(8 * t / nf)); erleA[q] += pyF[t]; erleB[q] += se; } // (song-only frames: echo removed by the linear stage)
      const s0 = t * H; R.inv(Er, Ei, ob); for (let i = 0; i < N; i++) e[s0 + i] += ob[i] * w[i];
      R.inv(Ar, Ai, ob); for (let i = 0; i < N; i++) yo[s0 + i] += ob[i] * w[i];
      if ((t & 63) === 0) prog(0.65 + 0.35 * t / nf);
    }
    // the first / last half frame got only one window: the room filter's own signals there
    const tail = nf ? (nf - 1) * H + N : 0;
    for (let i = 0; i < n; i++) if (i < H || i >= tail - H) { yo[i] = yh[i]; e[i] = y[i] - yh[i]; }
    const erle = []; for (let q = 0; q < 8; q++) erle.push(erleA[q] > 0 && erleB[q] > 0 ? +(10 * Math.log10(erleA[q] / erleB[q])).toFixed(1) : null);
    return { e, yh: yo, n, erle, channels: ch, guardedSec: +(nGuard * H / sr).toFixed(1), roomPct: +(100 * nRoom / Math.max(1, nf)).toFixed(1) };
  }

  const API = { clean, align, pbfdaf, suppress, stft2, rfftPlan, fft, B };
  if (typeof module !== 'undefined' && module.exports) module.exports = API; else root.HarmonyClean = API;
  // Worker: { id, x: Float32Array (reference), y: Float32Array (take), sr } -> progress messages, then { id, out, stats }
  if (typeof WorkerGlobalScope !== 'undefined' && root instanceof WorkerGlobalScope) {
    root.onmessage = (e) => { const m = e.data;
      try { const r = clean(null, m.y, m.sr, { src: m, onProg: (f) => root.postMessage({ id: m.id, prog: f }) }); root.postMessage({ id: m.id, out: r.out, stats: r.stats }, [r.out.buffer]); }
      catch (err) { root.postMessage({ id: m.id, error: String(err && err.stack || err) }); } };
  }
})(typeof self !== 'undefined' ? self : this);
