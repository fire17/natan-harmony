/* Harmony take-channel effects (v0.4.6): a zero-latency compressor for "ניקוי קול".
   Chromium's DynamicsCompressorNode looks ahead (measured: its output is 128 frames = 2.7 ms late), which would move the take against the
   song; this one reacts sample by sample with no delay at all: RMS detector (10 ms), gain computed in dB with a hard
   knee, attack / release smoothing on the gain reduction. Options { threshold dB, ratio, attack s, release s }. */
class HarmonyComp extends AudioWorkletProcessor {
  constructor(o) {
    super();
    const p = (o && o.processorOptions) || {};
    this.set(p);
    this.env = 0; this.g = 0; this.rc = Math.exp(-1 / (0.01 * sampleRate));
    this.port.onmessage = (e) => { if (e.data) this.set(e.data); };
  }
  set(p) {
    this.th = p.threshold != null ? p.threshold : -24;
    this.ratio = p.ratio || 2.5;
    this.at = Math.exp(-1 / ((p.attack || 0.01) * sampleRate));
    this.rl = Math.exp(-1 / ((p.release || 0.12) * sampleRate));
  }
  process(inputs, outputs) {
    const x = inputs[0], y = outputs[0];
    if (!x || !x.length) { for (const ch of y) ch.fill(0); return true; }
    const n = x[0].length, nc = x.length, k = 1 - 1 / this.ratio;
    let env = this.env, g = this.g;
    for (let i = 0; i < n; i++) {
      let p = 0; for (let c = 0; c < nc; c++) p += x[c][i] * x[c][i];
      env = this.rc * env + (1 - this.rc) * (p / nc);
      const over = 10 * Math.log10(env + 1e-12) - this.th, gr = over > 0 ? -over * k : 0;
      const co = gr < g ? this.at : this.rl; g = co * g + (1 - co) * gr;
      const lin = Math.pow(10, g / 20);
      for (let c = 0; c < y.length; c++) y[c][i] = x[c < nc ? c : 0][i] * lin;
    }
    this.env = env; this.g = g;
    return true;
  }
}
registerProcessor('harmony-comp', HarmonyComp);
