/* Harmony live practice (v0.8.0): one AudioWorklet node does both ends of a practice session, on one sample clock.
   - OUT: the target tone (the "drone"): a clean synth tone, the fundamental plus three soft harmonics, with smooth
     level ramps (30 ms) and smooth note changes / glides. Its phase is known for every frame.
   - IN: the microphone. With the phone's speaker the drone reaches the mic too, and a pitch detector would lock onto
     it instead of the voice. The drone is known exactly, so its echo is predicted and subtracted: while the drone
     plays ALONE (the "listen" second before each note), a least-squares fit finds, for each harmonic, how the room +
     speaker + mic change its level and phase (a cos / sin pair per harmonic — that is all a steady tone can undergo);
     from then on that prediction is removed from every mic sample. The voice is not part of the fit, so a voice on
     the very same note survives (a notch filter would remove it). A new note or level needs a new fit (the page asks).
   - The cleaned mic signal goes out in 256-frame blocks (5.3 ms) straight to the pitch Worker over a MessagePort
     (no main-thread hop), stamped with the context frame of its first sample. Raw blocks go to the page only while
     the user records the session.
   Messages in (port): { drone: { hz, level, glide: { to, frames, shape } }, at }, { learn: frames, at }, { reset: true },
   { record: bool }, { worker: MessagePort } (transferred), { stop: true } (the screen closed: the node ends). "at" = the context frame it takes effect (sample-exact; the
   page plans a whole exercise ahead, so the target it scores against is the very tone that played).
   Out (port): { learned: { reductionDb, frames, at } }, { raw, f0 }. */
const H = 4, HW = [1, 0.35, 0.18, 0.08], BLOCK = 256;

class HarmonyPractice extends AudioWorkletProcessor {
  constructor() {
    super();
    this.hz = 220; this.hzTo = 220; this.gFrames = 0; this.gLeft = 0; this.gFrom = 220; this.gShape = 'cos';
    this.amp = 0; this.ampTo = 0; this.ph = new Float64Array(H);
    this.c = new Float64Array(2 * H); this.cOk = false; // the fitted echo (cos, sin per harmonic)
    this.learnLeft = 0; this.AtA = new Float64Array(4 * H * H); this.Aty = new Float64Array(2 * H); this.yy = 0; this.learnN = 0;
    this.out = null; this.buf = new Float32Array(BLOCK); this.n = 0; this.f0 = 0;
    this.rec = false; this.raw = new Float32Array(BLOCK);
    this.q = []; // commands waiting for their frame
    this.alive = true; // { stop } (the screen closed): process() returns false and the node can be collected
    this.port.onmessage = (e) => {
      const m = e.data || {};
      if (m.worker) this.out = m.worker;
      if (m.at != null && (m.drone || m.learn)) { this.q.push(m); this.q.sort((a, b) => a.at - b.at); return; }
      this.apply(m);
    };
  }
  apply(m) {
      if (m.drone) {
        const d = m.drone;
        if (d.level != null) this.ampTo = Math.max(0, Math.min(1, d.level));
        if (d.hz != null && !d.glide) { this.hz = this.hzTo = d.hz; this.gLeft = 0; this.cOk = false; }
        if (d.glide) { this.gFrom = this.hz; this.hzTo = d.glide.to; this.gFrames = this.gLeft = Math.max(1, d.glide.frames | 0); this.gShape = d.glide.shape || 'cos'; this.cOk = false; }
      }
      if (m.learn) { this.learnLeft = m.learn | 0; this.AtA.fill(0); this.Aty.fill(0); this.yy = 0; this.learnN = 0; this.cOk = false; }
      if (m.reset) { this.cOk = false; this.learnLeft = 0; }
      if (m.clearQ) this.q = [];
      if (m.record != null) this.rec = !!m.record;
      if (m.stop) { this.alive = false; this.out = null; }
  }
  solve() { // AtA c = Aty (2H x 2H, Gaussian elimination with partial pivoting; a tiny ridge keeps it well posed)
    const n = 2 * H, A = new Float64Array(this.AtA), b = new Float64Array(this.Aty), tr = (() => { let s = 0; for (let i = 0; i < n; i++) s += A[i * n + i]; return s / n; })();
    for (let i = 0; i < n; i++) A[i * n + i] += 1e-6 * tr + 1e-12;
    for (let k = 0; k < n; k++) {
      let p = k; for (let i = k + 1; i < n; i++) if (Math.abs(A[i * n + k]) > Math.abs(A[p * n + k])) p = i;
      if (p !== k) { for (let j = 0; j < n; j++) { const t = A[k * n + j]; A[k * n + j] = A[p * n + j]; A[p * n + j] = t; } const t = b[k]; b[k] = b[p]; b[p] = t; }
      const d = A[k * n + k]; if (Math.abs(d) < 1e-18) return null;
      for (let i = k + 1; i < n; i++) { const f = A[i * n + k] / d; if (!f) continue; for (let j = k; j < n; j++) A[i * n + j] -= f * A[k * n + j]; b[i] -= f * b[k]; }
    }
    const x = new Float64Array(n);
    for (let i = n - 1; i >= 0; i--) { let s = b[i]; for (let j = i + 1; j < n; j++) s -= A[i * n + j] * x[j]; x[i] = s / A[i * n + i]; }
    return x;
  }
  process(inputs, outputs) {
    if (!this.alive) return false;
    const inp = inputs[0], mic = inp && inp[0], mic2 = inp && inp[1], out = outputs[0][0], len = out ? out.length : 128, cf = currentFrame, n2 = 2 * H, bas = new Float64Array(n2);
    for (let i = 0; i < len; i++) {
      while (this.q.length && this.q[0].at <= cf + i) this.apply(this.q.shift());
      // drone frequency (glide: raised cosine or linear in cents) and level (one-pole ramp, ~30 ms)
      if (this.gLeft > 0) { const u = 1 - (--this.gLeft) / this.gFrames, s = this.gShape === 'lin' ? u : 0.5 - 0.5 * Math.cos(Math.PI * u); this.hz = this.gFrom * Math.pow(this.hzTo / this.gFrom, s); }
      this.amp += (this.ampTo - this.amp) * 0.0007;
      let y = 0;
      for (let h = 0; h < H; h++) {
        const ph = this.ph[h]; const cs = Math.cos(ph), sn = Math.sin(ph);
        y += HW[h] * sn;
        bas[2 * h] = cs * this.amp * HW[h]; bas[2 * h + 1] = sn * this.amp * HW[h];
        let p = ph + 2 * Math.PI * this.hz * (h + 1) / sampleRate; if (p >= 2 * Math.PI) p -= 2 * Math.PI * Math.floor(p / (2 * Math.PI)); this.ph[h] = p;
      }
      if (out) out[i] = y * this.amp * 0.5;
      let x = mic ? (mic2 ? (mic[i] + mic2[i]) * 0.5 : mic[i]) : 0;
      const raw = x;
      if (this.learnLeft > 0) { // the drone alone: accumulate the normal equations of the echo fit
        for (let a = 0; a < n2; a++) { const ba = bas[a]; this.Aty[a] += ba * x; for (let b = a; b < n2; b++) this.AtA[a * n2 + b] += ba * bas[b]; }
        this.yy += x * x; this.learnN++;
        if (--this.learnLeft === 0) {
          for (let a = 0; a < n2; a++) for (let b = 0; b < a; b++) this.AtA[a * n2 + b] = this.AtA[b * n2 + a];
          const c = this.solve(); let res = this.yy;
          if (c) { let fit = 0; for (let a = 0; a < n2; a++) fit += c[a] * this.Aty[a]; res = Math.max(this.yy - fit, 1e-12); this.c.set(c); this.cOk = true; }
          this.port.postMessage({ learned: { reductionDb: c ? +(10 * Math.log10((this.yy + 1e-12) / res)).toFixed(1) : 0, frames: this.learnN, ok: !!c, at: cf + i } });
        }
      }
      if (this.cOk) { let e = 0; for (let a = 0; a < n2; a++) e += this.c[a] * bas[a]; x -= e; }
      if (!this.n) this.f0 = cf + i;
      this.buf[this.n] = x; if (this.rec) this.raw[this.n] = raw; this.n++;
      if (this.n === BLOCK) {
        if (this.out) { const d = this.buf; this.out.postMessage({ f0: this.f0, d, drone: this.ampTo > 0 ? this.hz : 0 }, [d.buffer]); this.buf = new Float32Array(BLOCK); }
        if (this.rec) { const r = this.raw; this.port.postMessage({ raw: r, f0: this.f0 }, [r.buffer]); this.raw = new Float32Array(BLOCK); }
        this.n = 0;
      }
    }
    return true;
  }
}
registerProcessor('harmony-practice', HarmonyPractice);
