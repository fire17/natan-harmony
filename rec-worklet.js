/* Harmony record-along (v0.4.0): mic input -> main thread, every sample tagged with its context frame.
   The page maps context frame c to song frame (c − T0F) − L (L = measured round-trip latency), so a take lands on the
   song timeline sample-exactly up to that calibration. Mono (stereo input is averaged). Blocks are batched (~43 ms)
   and transferred, never copied twice.
   v0.4.1: the frames are COUNTED, not read from currentFrame per quantum: process() runs once per render quantum, so
   the input is one continuous stream. In Chromium a single quantum now and then reports currentFrame one quantum low
   (seen while the song plays) — stamping by it put 128 samples on top of their neighbours and left a 2.7 ms hole.
   A mismatch for one quantum is absorbed (counted as "jit"); one that persists for 2 quanta is real and the count
   re-syncs to currentFrame (counted as "rs", a new block starts). No input at all (track ended) also breaks the run.
   v0.4.3: the A56 drifted with "slips" only — so also a long-window check: if the count and currentFrame disagree in
   >= 90 % of the quanta of the last second, frames were really lost: re-sync (the page leaves a hole there).
   Every message carries the running counters { jit, rs, miss } and the current offset currentFrame − count (off).
   v0.5.2: processorOptions { stereo: true } (the speaker-mode reference tap) keeps both channels: d = left, d2 = right. */
const BATCH = 128 * 16;

class HarmonyRec extends AudioWorkletProcessor {
  constructor(o) {
    super();
    this.st = !!(o && o.processorOptions && o.processorOptions.stereo); this.buf2 = this.st ? new Float32Array(BATCH) : null;
    this.buf = new Float32Array(BATCH); this.n = 0; this.f0 = 0;
    this.next = null; this.off = 0; this.offN = 0; this.jit = 0; this.rs = 0; this.miss = 0; this.win = 0; this.bad = 0; this.cur = 0;
    this.port.onmessage = (e) => { if (e.data === 'flush') this.flush(); };
  }
  flush() {
    if (!this.n) return;
    const d = this.buf.slice(0, this.n), d2 = this.st ? this.buf2.slice(0, this.n) : null;
    this.port.postMessage({ f0: this.f0, d, d2, jit: this.jit, rs: this.rs, miss: this.miss, off: this.cur }, d2 ? [d.buffer, d2.buffer] : [d.buffer]);
    this.n = 0;
  }
  process(inputs) {
    const inp = inputs[0];
    if (!inp || !inp.length || !inp[0]) { if (this.next != null) { this.flush(); this.next = null; this.miss++; } return true; }
    const L = inp[0], R = inp[1], len = L.length, cf = currentFrame;
    let f = this.next;
    if (f == null) f = cf;
    else {
      this.cur = cf - f; if (++this.win > 375) { this.win = 1; this.bad = 0; } if (cf !== f) this.bad++;
      if (cf !== f) {
        const off = cf - f;
        if ((this.offN && off === this.off) || (this.win >= 375 && this.bad >= 338)) { this.flush(); f = cf; this.rs++; this.offN = 0; this.bad = 0; this.cur = 0; } // persists: re-sync
        else { this.off = off; this.offN = 1; this.jit++; } // one quantum: keep counting
      } else this.offN = 0;
    }
    if (!this.n) this.f0 = f;
    if (this.st) for (let i = 0; i < len; i++) { this.buf[this.n + i] = L[i]; this.buf2[this.n + i] = R ? R[i] : L[i]; }
    else for (let i = 0; i < len; i++) this.buf[this.n + i] = R ? (L[i] + R[i]) * 0.5 : L[i];
    this.n += len; this.next = f + len;
    if (this.n + 128 > BATCH) this.flush();
    return true;
  }
}
registerProcessor('harmony-rec', HarmonyRec);
