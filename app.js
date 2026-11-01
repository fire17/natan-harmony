/* Harmony (הרמוניה) v0.6.0 — a small song library, 3–7 instrument stems per song, per-stem mute / volume / solo; key, chords, beat; lyrics the user pastes.

   ENGINE (why it looks like this)
   - Memory: six 4:21 stereo stems decoded to float32 are ~600 MB — too much for a mid-range phone. tools/make-song.sh
     cuts every stem into 8 s Ogg Opus chunks; the engine keeps only the chunk under the playhead and the next two
     decoded (≈ 3 × 6 × 3.1 MB ≈ 57 MB; a 7-stem song ≈ 66 MB) and schedules them back to back on the AudioContext clock.
   - Sync: every chunk of every stem is started with AudioBufferSourceNode.start(when, offset, duration) where `when`
     is computed in integer context frames from ONE anchor per play run (T0F = context frame of song frame 0).
     All stems of a chunk get the very same `when`, so they cannot drift apart, and nothing accumulates over time:
     chunk k always starts at T0F + k·CHUNK, whatever happened before.
   - Codec delay: each chunk file carries MARGIN frames of its own continuation on both sides; at load the engine
     decodes cal.opus (one impulse at a known frame, encoded exactly like the chunks) and measures the decoder's real
     offset D, so buffer frame (songFrame − fileStart + D) is always the right sample — whether or not this browser
     trims Opus pre-skip, and at any context sample rate.
   - Seams: adjacent chunks overlap by a 10 ms linear crossfade; the two sides carry the same (coherent) signal, so
     the sum is unity gain and lossy-coding differences at the cut are smeared instead of clicking.
   - Pause = fade out, then AudioContext.suspend(); resume = resume() + fade in. Every scheduled source keeps its
     place on the (frozen) context clock, so pause/resume is sync-exact by construction. Seek = fade out, new run.
   - Gains move with setTargetAtTime (no zipper / clicks); a master limiter (Shaket's: −1.5 dBFS, ratio 20) catches
     overs when channels are boosted up to 150 %.
   - Background (v0.2.4): paused AND hidden (page hidden, or the Android activity stopped) for 60 s -> the decoded
     window (~57 MB) is dropped and the AudioContext closed, so other apps (e.g. a TTS engine) get the memory back.
     The next play builds a fresh context + graph and decodes lazily from the kept position; mix, tempo, lyrics and
     calibration are untouched. Never while playing (background playback keeps everything). */
(() => {
  'use strict';

  const ANDROID = typeof window.Android !== 'undefined';
  const $ = (id) => document.getElementById(id);
  const el = (tag, cls, text) => { const e = document.createElement(tag); if (cls) e.className = cls; if (text != null) e.textContent = text; return e; };
  const clamp = (v, a, b) => Math.min(b, Math.max(a, v));
  // freeze an AudioParam at its current (automated) value, so the next ramp starts from where it really is: no jumps
  const hold = (p, t) => { if (p.cancelAndHoldAtTime) p.cancelAndHoldAtTime(t); else { p.cancelScheduledValues(t); p.setValueAtTime(p.value, t); } };
  const fmt = (s) => { s = Math.max(0, Math.floor(s)); return Math.floor(s / 60) + ':' + String(s % 60).padStart(2, '0'); };
  const store = {
    get(k) { try { return JSON.parse(localStorage.getItem(k)); } catch (e) { return null; } },
    set(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch (e) { /* private mode / quota: mix just isn't remembered */ } try { pkNote(k); } catch (e) { /* before the pack module (boot) */ } },
  };

  // (v0.6.0) a per-song setting / a device setting changed: the open song's pack is saved (see PK)
  function pkNote(k) { const m = SONG_KEY.exec(k); if (m) PK.mark(m[2], { user: true }); else if (GLOBAL_KEY.test(k) && E.song) PK.mark(E.song.id, { user: true }); }

  const LOOKAHEAD = 2;          // chunks decoded + scheduled beyond the one under the playhead
  const LEAD = 0.1;             // s between "go" and the first sample (room to schedule; a just-resumed clock can jump ~60 ms)
  const TICK_MS = 250;          // scheduler period (a chunk is 8 s: dozens of ticks of slack)
  const SAFETY = 0.05;          // s: a late chunk joins at least this far in the future
  const FADE_TC = 0.012;        // play / seek fade-in time constant (s)
  const FADE_OUT = 0.035;       // pause / seek: linear ramp to exactly 0 over this long (s), then stop / suspend
  const GAIN_TC = 0.03;         // mute / solo / preset time constant (s): smooth, no click
  const SLIDE_TC = 0.05;        // slider drag time constant (s)
  const VOL_MAX = 150;

  // ---------------------------------------------------------------- engine
  const E = {
    ctx: null, SR: 48000, song: null, base: '', D: 0,
    Lf: 0, Xf: 0, Mf: 0, durF: 0,       // chunk / crossfade / margin / song length, in context frames
    stems: [], bus: null, out: null, lim: null, trim: null,
    chunks: new Map(),                  // k -> { k, ready, promise, bufs[], bytes }
    run: null, runSeq: 0, runs: [],     // the current play run + a short log (tests)
    pausedF: 0, playing: false, suspendTimer: 0,
    bytes: 0, peakBytes: 0, decodes: 0, lateJoins: 0, errors: 0,
    rate: 1, semi: 0, stretch: null, stretchT: null, stretchReady: null, routed: null, // tempo (v0.2.2): song tempo × rate, pitch kept
    ready: false, bg: false, released: false, releases: 0, idleSince: 0, idleTimer: 0, // background release (v0.2.4)
  };
  // Tempo r != 1: every stem source plays at playbackRate r (all stems share one clock: still sample-locked), and ONE
  // pitch shifter on the summed bus (stretch-worklet.js: WSOLA + resampler) changes the pitch by p = 2^(s/12) / r
  // (v0.5.3: s = transpose in semitones; s = 0 brings the pitch back to the original). The bus sits after the per-stem
  // gains, so mute / solo / volume act before it. p = 1 (100 %, no transpose): the shifter is disconnected (zero cost).
  // (v0.5.3) the take channel ("ההקלטה שלי") has its own bus and shifter, p_T = 2^((s − s_take)/12) / r: a take recorded
  // at transpose s_take is in that key already, so it is never shifted twice. Each path ends in a delay node so both
  // reach the output with the same delay: L = max(latency A, latency T); a bypassed path waits L.
  // Shifter delay in frames: what the worklet measures (per p; mean of its first splices), until then the real-time fit
  // 1750 + 4100 / p at 48 kHz (v0.5.3: 40 runs, transpose −6..+6 × tempo 75 / 100 / 125 %, p 0.57–1.89, within ±100
  // frames: .work harmony-e2e/t/latrt.json). The display clock uses it until the measurement arrives (~0.6 s).
  const latCache = {};
  const pKey = (p) => p.toFixed(5);
  // (v0.5.3) with a transpose the shifter is the phase vocoder (harmony-pv): a constant delay of 2048 frames, exact for
  // every transient (WSOLA's splice + resampler moves them by up to ±12 ms: a take recorded in a transposed key could not
  // be placed within 2 ms); tempo alone keeps the WSOLA (unchanged sound)
  const latOf = (p, kind) => (Math.abs(p - 1) < 1e-9 ? 0 : kind === 'pv' ? 2048 : latCache[pKey(p)] != null ? latCache[pKey(p)] : (1750 + 4100 / p) * E.SR / 48000);
  const runLat = (r) => (r ? (r.latA || 0) + (r.dA || 0) : 0); // what the stems' path adds before the output, frames
  const stretchLatF = () => runLat(E.run); // (kept for tests: the running path's delay)
  function route(r) {
    const key = r ? [r.pA, r.pT, r.pD, r.dA, r.dT, r.dD].map((x) => +(x || 0).toFixed(6)).join('/') + r.kind : '1/1/0/0';
    if (E.routed === key) return;
    [E.bus, E.busT, E.busD, E.stretch, E.stretchT, E.pvA, E.pvT, E.pvD, E.dlyA, E.dlyT, E.dlyD].forEach((n) => { if (n) try { n.disconnect(); } catch (e) { /* not connected */ } });
    // (v0.5.3) the drums channel feeds the drums' bus only while transposed (its own path keeps the delay of the others)
    const dr = E.stems.find((st) => st.id === 'drums'), sep = !!(r && r.pD != null);
    if (dr) { try { dr.gain.disconnect(); } catch (e) { /* none */ } dr.gain.connect(dr.analyser); dr.gain.connect(sep ? E.busD : E.bus); }
    const path = (bus, sh, p, dl, d) => { // bus -> [shifter] -> [delay] -> out
      let x = bus; if (p !== 1 && sh) { x.connect(sh); x = sh; }
      if (d > 0) { dl.delayTime.value = d / E.SR; x.connect(dl); x = dl; }
      x.connect(E.out);
    };
    if (!r) { E.bus.connect(E.out); E.busT.connect(E.out); E.busD.connect(E.out); E.routed = key; return; }
    const pv = r.kind === 'pv'; path(E.bus, pv ? E.pvA : E.stretch, r.pA, E.dlyA, r.dA); path(E.busT, pv ? E.pvT : E.stretchT, r.pT, E.dlyT, r.dT);
    if (sep) path(E.busD, E.pvD, r.pD, E.dlyD, r.dD); else E.busD.connect(E.out);
    E.routed = key;
  }

  // a shifter's measurement: cached per p; the take path's delay follows the stems' path so both stay together
  // (a smooth 150 ms glide, only for a difference > 0.5 ms); for a recording, the mean over ALL splices of the take
  function onShiftLat(which, d) {
    const r = E.run; if (!d || !r || d.gen !== (which === 'A' ? r.genA : r.genT)) return;
    if (Number.isFinite(d.latency)) { const p = which === 'A' ? r.pA : r.pT; if (r.kind !== 'pv') latCache[pKey(p)] = d.latency; if (which === 'A') r.latAm = d.latency; else r.latTm = d.latency; }
    if (Number.isFinite(d.latAll) && which === 'A') { r.latAll = d.latAll; r.latAllN = d.n; }
    if (Number.isFinite(d.latency) && E.dlyT && r.pT !== undefined) {
      const lA = (r.latAm != null ? r.latAm : r.latA) + r.dA, lT = r.pT === 1 ? 0 : (r.latTm != null ? r.latTm : r.latT), want = Math.max(0, lA - lT);
      if (Math.abs(want - r.dT) > E.SR * 0.0005 && (r.dT > 0 || r.pT === 1)) { r.dT = want; try { const g = E.dlyT.delayTime; hold(g, E.ctx.currentTime); g.setTargetAtTime(want / E.SR, E.ctx.currentTime, 0.05); } catch (e) { /* gone */ } }
    }
  }

  function makeCtx() {
    const AC = window.AudioContext || window.webkitAudioContext;
    let ctx;
    // 48 kHz = the chunks' own rate: no resampling at decode, exact frame arithmetic. Falls back to the device rate.
    try { ctx = new AC({ latencyHint: 'playback', sampleRate: 48000 }); } catch (e) {
      try { ctx = new AC({ latencyHint: 'playback' }); } catch (e2) { ctx = new AC(); }
    }
    if (ctx.state === 'running') ctx.suspend(); // (Android WebView may auto-start) silent until the first tap
    return ctx;
  }

  function buildGraph() {
    const ctx = E.ctx;
    const gain = (v) => { const g = ctx.createGain(); g.gain.value = v; return g; };
    E.bus = gain(1); E.busT = gain(1); E.busD = gain(1); // (v0.5.3) the take channel's own bus; the drums' bus (never transposed)
    E.dlyA = ctx.createDelay(1); E.dlyT = ctx.createDelay(1); E.dlyD = ctx.createDelay(1);
    E.out = gain(0); // play / pause / seek fades
    E.lim = ctx.createDynamicsCompressor();
    E.lim.threshold.value = -1.5; E.lim.knee.value = 0; E.lim.ratio.value = 20;
    E.lim.attack.value = 0.002; E.lim.release.value = 0.15;
    E.trim = gain(1 / LIM_MAKEUP_EST); // cancels the compressor's built-in makeup (measured below)
    E.vol = gain(1); // (v0.5.1) the app's own master level: lowered in speaker mode when the song reaches the mic too loud;
    // the speaker-mode reference is tapped AFTER it, so it stays exactly what the phone plays
    E.bus.connect(E.out); E.busT.connect(E.out); E.busD.connect(E.out); E.out.connect(E.lim); E.lim.connect(E.trim); E.trim.connect(E.vol); E.vol.connect(ctx.destination);
    E.stretchReady = (ctx.audioWorklet ? ctx.audioWorklet.addModule('stretch-worklet.js') : Promise.reject(new Error('no worklet')))
      .then(() => {
        const mk = (which) => { const n = new AudioWorkletNode(ctx, 'harmony-stretch', { numberOfInputs: 1, numberOfOutputs: 1, outputChannelCount: [2], channelCount: 2, channelCountMode: 'explicit' });
          n.port.onmessage = (e) => onShiftLat(which, e.data); return n; };
        E.stretch = mk('A'); E.stretchT = mk('T');
        const mkPV = (which) => { const n = new AudioWorkletNode(ctx, 'harmony-pv', { numberOfInputs: 1, numberOfOutputs: 1, outputChannelCount: [2], channelCount: 2, channelCountMode: 'explicit' });
          n.port.onmessage = (e) => onShiftLat(which, e.data); return n; };
        E.pvA = mkPV('A'); E.pvT = mkPV('T'); E.pvD = mkPV('D');
        return true;
      }, () => false);
    E.fxReady = ctx.audioWorklet ? ctx.audioWorklet.addModule('fx-worklet.js').then(() => true, () => false) : Promise.resolve(false);
    E.stems = E.song.stems.map(stemNode);
    measureMakeup();
  }

  function stemNode(s) { // one channel: gain -> (meter analyser) + mix bus
    const ctx = E.ctx, g = ctx.createGain(), an = ctx.createAnalyser();
    g.gain.value = 0; an.fftSize = 512; an.smoothingTimeConstant = 0;
    g.connect(an); g.connect(s.take ? E.busT : E.bus); // (v0.5.3) the take channel: its own bus (its own pitch factor)
    const n = { id: s.id, label: s.label, gain: g, analyser: an, buf: new Float32Array(an.fftSize), level: 0 };
    if (s.take) { // the record-along channel: its effects sit between the sources and the channel gain
      n.fx = fxBuild(ctx, E.fxReady); n.fx.out.connect(g); n.inp = n.fx.inp;
      n.fx.set(REC.fxOf(REC.active), true); n.fx.setRate(E.rate);
    }
    return n;
  }

  // ---------------------------------------------------------------- take-channel effects (v0.4.6)
  // "אפקטים" on the "ההקלטה שלי" channel, during playback only — the stored take is never changed. One graph per take
  // channel per AudioContext (never per chunk):
  //   in ┬ raw ─────────────────────────────────────────────────────────────────────────┐
  //      └ HP 90 Hz → −4 dB @500 Hz → +2 dB @2.5 kHz → −5 dB shelf @8 kHz → compressor → +3 dB ┴ pre ┬→ (dry) ─→ out
  //                                    pre → reverb send → 300 Hz–6 kHz → convolver (plate, 1.1 s) ┤
  //                                    pre → echo send → 300 Hz–4 kHz → delay (1 beat ÷ tempo) ↺ 20 % ┘
  // The dry path has no delay and no look-ahead (the compressor is fx-worklet.js, not DynamicsCompressorNode, which
  // delays its output 128 frames = 2.7 ms, measured), so the take stays sample-aligned with the song with effects on. All of it is before the channel
  // gain (volume / mute / solo include the effects) and before the mix bus: at tempo ≠ 100 % the take and its effects
  // pass the same pitch shifter as the stems; the echo stays one beat of the song at the playing tempo.
  // Settings per take (t.fx): on (default off), reverb / echo wet %, clean (HP + EQ + compressor).
  const FX_DEF = { on: false, reverb: 18, echo: 9, clean: true };
  // reverb control % -> send gain (v0.4.7). v0.4.6 used gain = % / 100: on a sung vowel the tail 50–300 ms after a note
  // was −24 dB vs the dry voice at 18 % and only −9 dB at 100 %, too little to hear under the band ("no difference").
  // Now gain = 0.18 · (% / 18)^1.2: 18 % is unchanged (the subtle default), 100 % = +3 dB (tail ≈ −6 dB, a clear room);
  // in between it rises faster than before (30 % +0.9 dB, 50 % +1.8 dB, 75 % +2.5 dB vs v0.4.6). Saved values keep their
  // %, so 18 stays exactly 18; below 18 % it is a little quieter than before (5 % −2.2 dB).
  const rvGain = (p) => (p > 0 ? 0.18 * Math.pow(clamp(p, 0, 100) / 18, 1.2) : 0);
  function plateIR(ctx) { // 1.5 s stereo: decorrelated noise, exponential decay (RT60 1.1 s), 30 ms pre-delay, unit energy
    const SR = ctx.sampleRate, n = Math.round(1.5 * SR), pre = Math.round(0.03 * SR), b = ctx.createBuffer(2, n, SR);
    let seed = 0x9e3779b9;
    const rnd = () => { seed |= 0; seed = (seed + 0x6d2b79f5) | 0; let t = Math.imul(seed ^ (seed >>> 15), 1 | seed); t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t; return ((t ^ (t >>> 14)) >>> 0) / 4294967296 * 2 - 1; };
    for (let c = 0; c < 2; c++) {
      const x = b.getChannelData(c); let e = 0;
      for (let i = pre; i < n; i++) { x[i] = rnd() * Math.exp(-6.9078 * (i - pre) / (1.1 * SR)); e += x[i] * x[i]; }
      const k = 1 / Math.sqrt(e); for (let i = pre; i < n; i++) x[i] *= k;
    }
    return b;
  }
  function fxBuild(ctx, ready) {
    const G = (v) => { const g = ctx.createGain(); g.gain.value = v; return g; };
    const BW = -3.0103; /* Web Audio lowpass/highpass Q is in dB: -3.01 dB = linear 0.7071 = Butterworth (12 dB/oct, no bump) */
    const F = (type, f, gain, q) => { const b = ctx.createBiquadFilter(); b.type = type; b.frequency.value = f; if (gain != null) b.gain.value = gain; if (q != null) b.Q.value = q; return b; };
    const inp = G(1), raw = G(1), clean = G(0), pre = G(1), out = G(1);
    const hp = F('highpass', 90, null, BW), p500 = F('peaking', 500, -4, 1), p2k5 = F('peaking', 2500, 2, 1), hs = F('highshelf', 8000, -5);
    const cin = G(1), cout = G(1), makeup = G(Math.pow(10, 3 / 20));
    inp.connect(raw); raw.connect(pre);
    inp.connect(hp); hp.connect(p500); p500.connect(p2k5); p2k5.connect(hs); hs.connect(cin); cin.connect(cout); cout.connect(makeup); makeup.connect(clean); clean.connect(pre);
    if (ready) ready.then((ok) => { // the compressor joins once its worklet module is loaded on this context
      if (!ok) return;
      try {
        const comp = new AudioWorkletNode(ctx, 'harmony-comp', { numberOfInputs: 1, numberOfOutputs: 1, outputChannelCount: [1], processorOptions: { threshold: -24, ratio: 2.5, attack: 0.01, release: 0.12 } });
        cin.disconnect(); cin.connect(comp); comp.connect(cout); fx.comp = comp;
      } catch (e) { /* stays uncompressed */ }
    });
    pre.connect(out); // dry
    const rv = G(0), rhp = F('highpass', 300, null, BW), rlp = F('lowpass', 6000, null, BW), conv = ctx.createConvolver();
    conv.normalize = false; conv.buffer = plateIR(ctx);
    pre.connect(rv); rv.connect(rhp); rhp.connect(rlp); rlp.connect(conv); conv.connect(out);
    const ev = G(0), ehp = F('highpass', 300, null, BW), elp = F('lowpass', 4000, null, BW), dl = ctx.createDelay(4), fb = G(0.2), sum = G(1), cyc = ctx.createDelay(4);
    /* band-limit once, then repeats at exact beat multiples: echo = dl(x) + 0.2 * cyc(echo). Chromium adds one render
       quantum (128 frames) to a DelayNode that sits in a cycle, so the cycle's own delay is set one quantum shorter. */
    pre.connect(ev); ev.connect(ehp); ehp.connect(elp); elp.connect(dl); dl.connect(sum); sum.connect(fb); fb.connect(cyc); cyc.connect(sum); sum.connect(out);
    const fx = {
      inp, out, nodes: { raw, clean, rv, ev, dl, cyc, conv, hp, p500, p2k5, hs, makeup },
      set(v, now) {
        const on = !!v.on, cl = on && v.clean !== false, t = ctx.currentTime, put = (p, x) => { if (now) p.value = x; else { p.cancelScheduledValues(t); p.setValueAtTime(p.value, t); p.setTargetAtTime(x, t, 0.02); } };
        put(raw.gain, cl ? 0 : 1); put(clean.gain, cl ? 1 : 0);
        put(rv.gain, on ? rvGain(v.reverb) : 0); put(ev.gain, on ? clamp(v.echo, 0, 100) / 100 : 0);
      },
      setRate(r) { const bpm = (HV.A && HV.A.bpm) || 100; const d = Math.min(3.9, 60 / bpm / (r || 1)); dl.delayTime.value = d; cyc.delayTime.value = Math.max(0, d - 128 / ctx.sampleRate); },
    };
    return fx;
  }
  // Chromium's compressor applies makeup = (1 / gain at 0 dBFS)^0.6; −1.5 dB / ratio 20 / knee 0 ≈ 1.10. Measured at
  // steady state offline (a −20 dBFS sine through an identical compressor), so material below −1.5 dBFS passes at unity.
  const LIM_MAKEUP_EST = Math.pow(1 / Math.pow(10, (-1.5 + 1.5 / 20) / 20), 0.6);
  function measureMakeup() {
    const OAC = window.OfflineAudioContext || window.webkitOfflineAudioContext;
    if (!OAC) return;
    try {
      const sr = 44100, n = sr, oc = new OAC(1, n, sr), b = oc.createBuffer(1, n, sr), x = b.getChannelData(0);
      for (let i = 0; i < n; i++) x[i] = 0.1 * Math.sin(2 * Math.PI * 1000 * i / sr);
      const s = oc.createBufferSource(), c = oc.createDynamicsCompressor();
      ['threshold', 'knee', 'ratio', 'attack', 'release'].forEach((k) => { c[k].value = E.lim[k].value; });
      s.buffer = b; s.connect(c); c.connect(oc.destination); s.start(0);
      oc.startRendering().then((r) => {
        const y = r.getChannelData(0); let si = 0, so = 0;
        for (let i = n - (sr >> 2); i < n; i++) { si += x[i] * x[i]; so += y[i] * y[i]; }
        const v = Math.sqrt(so / si);
        if (v > 0.5 && v < 8) { E.makeup = v; E.trim.gain.setTargetAtTime(1 / v, E.ctx.currentTime, 0.05); }
      }, () => {});
    } catch (e) { /* estimate stays */ }
  }

  function decode(ab) {
    return new Promise((res, rej) => {
      const p = E.ctx.decodeAudioData(ab, res, rej);
      if (p && p.then) p.then(res, rej);
    });
  }
  async function fetchBuf(name) {
    const r = await fetch(E.base + name);
    if (!r.ok) throw new Error(name + ' ' + r.status);
    return r.arrayBuffer();
  }

  // Decoder offset: the impulse sits at cal.peakFrame (song rate); wherever this decoder puts it, D = found − expected.
  async function calibrate() {
    const b = await decode(await fetchBuf(E.song.cal.file));
    const x = b.getChannelData(0), exp = Math.round(E.song.cal.peakFrame * E.SR / E.song.sampleRate);
    let at = 0, m = 0;
    for (let i = 0; i < x.length; i++) { const a = Math.abs(x[i]); if (a > m) { m = a; at = i; } }
    E.D = m > 0.1 && Math.abs(at - exp) < E.Mf / 2 ? at - exp : 0;
    E.calPeak = m;
  }

  const bufBytes = (b) => b.length * b.numberOfChannels * 4;
  function loadChunk(k) {
    let c = E.chunks.get(k);
    if (c) return c.promise;
    c = { k, ready: false, bufs: null, bytes: 0 };
    E.chunks.set(k, c);
    const kk = String(k).padStart(2, '0');
    // the record-along channel ("mine", v0.4.0) comes from IndexedDB (the active take), the stems from their Opus chunks
    c.promise = Promise.all(E.song.stems.map((s) => (s.take ? REC.chunkBuf(k) : fetchBuf(`${s.id}-${kk}.${E.song.ext}`).then(decode))))
      .then((bufs) => {
        E.decodes++;
        if (E.chunks.get(k) !== c) return c; // evicted while decoding: drop it
        c.bufs = bufs; c.ready = true;
        c.bytes = bufs.reduce((a, b) => a + (b ? bufBytes(b) : 0), 0);
        E.bytes += c.bytes; E.peakBytes = Math.max(E.peakBytes, E.bytes);
        return c;
      }, (err) => { if (E.chunks.get(k) === c) { E.errors++; E.chunks.delete(k); } throw err; }); // (evicted: not an error)
    return c.promise;
  }
  function evict(keepFrom, keepTo, keep2) {
    E.chunks.forEach((c, k) => {
      if (k >= keepFrom && k <= keepTo) return;
      if (keep2 && k >= keep2[0] && k <= keep2[1]) return; // (v0.5.3) the loop's start stays decoded
      if (c.ready) E.bytes -= c.bytes;
      E.chunks.delete(k); // sources still playing it keep their own reference until they end
    });
  }

  const chunkAt = (f) => clamp(Math.floor(f / E.Lf), 0, E.song.chunks - 1);
  const ctxF = () => Math.round(E.ctx.currentTime * E.SR);
  function posF() {
    loopAdopt();
    const r = E.run;
    if (!r || r.T0F == null) return E.pausedF;
    return clamp((ctxF() - r.T0F) * r.rate, r.startF, E.durF);
  }

  // Schedule chunk k of run r from song frame fromF on (all stems share `when`).
  function schedule(r, k, fromF) {
    const c = E.chunks.get(k);
    const { Lf, Xf, Mf, SR } = E;
    const cF = k ? k * Lf - Xf : 0, eF = Math.min((k + 1) * Lf, E.durF), sF = Math.max(0, k * Lf - Mf);
    const f0 = Math.max(cF, fromF);
    if (f0 >= eF) { r.scheduled.add(k); return; }
    const t = (f) => (r.T0F + f / r.rate) / SR; // context time of song frame f in this run
    const when = t(f0), off = Math.max(0, f0 - sF + E.D) / SR, len = (eF - f0) / SR;
    const fadeIn = k > 0 && f0 < k * Lf, fadeOut = eF < E.durF;
    E.stems.forEach((st, i) => {
      if (!c.bufs[i]) return; // a take with nothing recorded in this chunk
      const src = E.ctx.createBufferSource(), fade = E.ctx.createGain(), g = fade.gain;
      src.buffer = c.bufs[i]; src.playbackRate.value = r.rate;
      if (fadeIn) { g.setValueAtTime((f0 - cF) / Xf, when); g.linearRampToValueAtTime(1, t(k * Lf)); }
      else g.setValueAtTime(1, when);
      if (fadeOut) {
        const a = Math.max(f0, eF - Xf);
        if (a > f0 || !fadeIn) g.setValueAtTime(a > f0 ? 1 : (eF - f0) / Xf, t(a));
        g.linearRampToValueAtTime(0, t(eF));
      }
      src.connect(fade); fade.connect(runGain(r, i, st)); // (-> per-run gain -> channel; the take channel: through its effects)
      src.onended = () => { r.sources.delete(src); try { fade.disconnect(); } catch (e) { /* gone */ } };
      r.sources.add(src);
      src.start(when, off, len);
    });
    r.scheduled.add(k);
  }

  // Keeps the window [chunk under playhead .. +LOOKAHEAD] decoded and scheduled; evicts everything else.
  function tick() {
    loopAdopt();
    const r = E.run;
    if (!E.song || E.released) return;
    const p = posF(), c = chunkAt(p), last = Math.min(E.song.chunks - 1, c + LOOKAHEAD);
    evict(c, last, loopLive() ? [chunkAt(LOOP.Fs), Math.min(E.song.chunks - 1, chunkAt(LOOP.Fs) + 1)] : null);
    for (let k = c; k <= last; k++) {
      const ch = E.chunks.get(k);
      if (!ch || !ch.ready) { loadChunk(k).then(tick, () => {}); continue; }
      if (r && r.T0F != null && E.playing && !r.scheduled.has(k) && !r.next) { // (a run handing over to its loop repeat schedules nothing more)
        // normally a chunk is scheduled seconds before its start; a late one (decode stall) joins in progress, still
        // on the same clock: a dropout, never a drift
        const cF = k ? k * E.Lf - E.Xf : 0, earliest = Math.round((ctxF() - r.T0F + SAFETY * E.SR) * r.rate);
        if (earliest > Math.max(cF, r.startF)) { E.lateJoins++; (E.lateLog = E.lateLog || []).push([k, earliest / E.SR, cF / E.SR, r.startF / E.SR, E.ctx.state]); }
        schedule(r, k, Math.max(r.startF, earliest));
      }
    }
    if (r && r.next) for (let k = chunkAt(r.next.startF); k <= Math.min(E.song.chunks - 1, chunkAt(r.next.startF) + LOOKAHEAD); k++) { // the repeat's later chunks
      const ch = E.chunks.get(k); if (ch && ch.ready && !r.next.scheduled.has(k)) schedule(r.next, k, Math.max(r.next.startF, k ? k * E.Lf - E.Xf : 0));
    }
    loopTick(r);
    if (E.playing && r && r.T0F != null && p >= E.durF) finish();
  }

  function fadeOut() {
    const g = E.out.gain, now = E.ctx.currentTime;
    hold(g, now); g.linearRampToValueAtTime(0, now + FADE_OUT);
    E.quietAt = now + FADE_OUT;
    return E.quietAt;
  }
  function stopRun(r, at) {
    if (!r) return;
    r.sources.forEach((s) => { try { s.stop(at); } catch (e) { /* not started / already stopped */ } });
    r.ended = E.ctx.currentTime;
    if (r.next) { const n = r.next; r.next = null; stopRun(n, at); } // (v0.5.3) a loop repeat already scheduled
    if (r.clicks) r.clicks.forEach((c) => { try { c.stop(at); } catch (e) { /* done */ } });
    if (r.g) { const g = r.g; setTimeout(() => g.forEach((x) => { try { x.disconnect(); } catch (e) { /* gone */ } }), Math.max(0, (at || 0) - E.ctx.currentTime) * 1000 + 500); }
  }
  // (v0.5.3) every run has one gain per channel between its sources and the channel: a loop seam crossfades two runs
  function runGain(r, i, st) {
    r.g = r.g || [];
    if (!r.g[i]) { const g = E.ctx.createGain(); g.gain.value = r.gainStart != null ? r.gainStart : 1; g.connect(st.inp || st.gain); r.g[i] = g; if (r.ramp) r.ramp(g.gain); }
    return r.g[i];
  }

  // ---------------------------------------------------------------- section loop (v0.5.3)
  function loopLoad() {
    const v = store.get(LOOP_KEY()) || {}; LOOP.a = Number.isInteger(v.a) ? v.a : null; LOOP.b = Number.isInteger(v.b) ? v.b : null; LOOP.on = !!v.on && LOOP.a != null;
    LOOP.count = store.get('harmony.loopcount.v1') === true; loopCalc();
  }
  function loopCalc() { const r = loopRange(); LOOP.Fs = r ? r[0] : 0; LOOP.Fe = r ? r[1] : 0; loopUI(); }
  // set the range (line indices) and / or on-off; a repeat already scheduled is redone from the current spot
  function loopSet(a, b, on) {
    if (a !== undefined) { LOOP.a = a; LOOP.b = b; }
    if (on !== undefined) LOOP.on = on && LOOP.a != null;
    store.set(LOOP_KEY(), LOOP.a == null ? null : { a: LOOP.a, b: LOOP.b, on: LOOP.on });
    const oldFs = LOOP.Fs, oldFe = LOOP.Fe; loopCalc();
    const r = E.run, playing = E.playing && r && r.T0F != null;
    if (playing && r.next && (!loopLive() || oldFs !== LOOP.Fs || oldFe !== LOOP.Fe)) seek(posF() / E.SR); // drop the scheduled repeat
    if (playing && loopLive()) { const p = posF(); if (p < LOOP.Fs - E.SR * 0.5 || p >= LOOP.Fe) seek(LOOP.Fs / E.SR); } // outside the range: start at it
  }
  const loopName = () => (LOOP.a == null ? '' : LOOP.a === LOOP.b ? 'שורה ' + (LOOP.a + 1) : 'שורות ' + '\u2066' + (LOOP.a + 1) + '–' + (LOOP.b + 1) + '\u2069'); // (LTR isolate: "3–6", never "6–3")
  function loopUI() {
    if (!$('loopRow')) return;
    const has = LOOP.a != null, ok = LOOP.Fe > LOOP.Fs, name = loopName();
    $('loopRow').hidden = !has; $('miniLoopRow').hidden = !has; $('lyrLoop').hidden = !has;
    const txt = has ? name + (ok ? '' : ' (לא מתוזמנות)') : '';
    $('loopTxt').replaceChildren(document.createTextNode('🔁 ' + txt)); $('miniLoopTxt').replaceChildren(document.createTextNode(txt));
    ['lyrLoop', 'miniLoop'].forEach((id) => { const x = $(id); const lab = 'חזרה על ' + (name || 'קטע') + ': ' + (LOOP.on ? 'פועלת' : 'כבויה'); x.classList.toggle('on', LOOP.on); x.setAttribute('aria-pressed', String(LOOP.on)); x.setAttribute('aria-label', lab); x.title = lab; });
    const c = $('loopCount'); c.textContent = 'ספירה לפני כל חזרה: ' + (LOOP.count ? 'פועלת' : 'כבויה'); c.setAttribute('aria-pressed', String(LOOP.count)); c.classList.toggle('on', LOOP.count);
    // the rows inside the range
    (LY.rows || []).forEach((r) => { if (!r.el) return; const t = r.t0, inR = has && ok && Number.isFinite(t) && t * E.SR >= LOOP.Fs - 1 && t * E.SR < LOOP.Fe - E.SR * 0.05; r.el.classList.toggle('in-loop', !!inR); });
  }

  // A range of lines [a, b] (numbers only). Song frames: from 0.12 s before line a's start to the same beat phase a
  // whole number of bars later, at / after line b's end (the chords up to the next line included) — so the repeat keeps
  // the beat. Sample-locked: the repeat is a new run on the same context clock whose song frame Fs starts exactly where the
  // old run reaches Fe (T0F' = T0F + (Fe − Fs) / rate [+ a count-in bar]); the two cross-fade over 10 ms around the
  // seam (per-run channel gains), before the mix bus — the pitch shifter and the effects see one continuous signal.
  // Off while recording (the take runs straight); the range is remembered per song.
  const LOOP = { a: null, b: null, on: false, count: false, Fs: 0, Fe: 0, X: 0.005 };
  const LOOP_MIN_S = 1.5; // (v0.7.2) the shortest repeat
  const LOOP_KEY = () => 'harmony.loop.v1.' + E.song.id;
  function loopRange() { // -> [Fs, Fe] frames or null
    if (LOOP.a == null || LOOP.b == null || !LY.rows || !HV.A) return null;
    // (v0.7.0) no lyrics: the song's own lines (its vocal phrases), so a line to practise can repeat without lyrics too
    const RW = LY.lines.length ? LY.rows : (HV.A.phrases || []).map((p, i) => ({ kind: 'line', i, t0: p.t0, c1: p.t1 }));
    const ra = RW.find((x) => x.kind === 'line' && x.i === LOOP.a), rb = RW.find((x) => x.kind === 'line' && x.i === LOOP.b);
    if (!ra || !rb || !Number.isFinite(ra.t0) || !Number.isFinite(rb.c1)) return null;
    // start just before line a (its pickup included); end at the SAME beat phase a whole number of bars later, at or
    // after the end of line b — the repeat lands on the beat it left
    const down = HV.A.downbeats || [], s0 = Math.max(0, ra.t0 - 0.12), t1 = rb.c1;
    let s1 = t1;
    if (down.length > 1) { let k1 = 0; for (let k = 1; k < down.length; k++) if (Math.abs(down[k] - s0) < Math.abs(down[k1] - s0)) k1 = k;
      const ph = s0 - down[k1]; for (let k = k1 + 1; k < down.length; k++) if (down[k] + ph >= t1 - 0.05) { s1 = down[k] + ph; break; } }
    // (v0.7.2) never a sliver: at least LOOP_MIN_S (whole bars added at the same beat phase; no bars: plain seconds)
    if (!(s1 > s0)) s1 = s0;
    const barS = down.length > 1 ? (down[down.length - 1] - down[0]) / (down.length - 1) : 0;
    while (s1 - s0 < LOOP_MIN_S) s1 += barS > 0.2 ? barS : LOOP_MIN_S - (s1 - s0);
    if (s0 * E.SR >= E.durF - E.SR * LOOP_MIN_S) return null; // (a line in the last 1.5 s of the song: nothing to repeat)
    return [Math.round(s0 * E.SR), Math.min(E.durF, Math.round(s1 * E.SR))];
  }
  const loopLive = () => LOOP.on && !REC.on && !REC.busy && LOOP.Fe > LOOP.Fs;
  function loopAdopt() { // the repeat's run takes over once the context clock reaches its seam
    const r = E.run; if (!r || !r.next || !E.ctx) return;
    if (ctxF() >= r.next.seamF) { const n = r.next; r.next = null; E.run = n; (E.loopLog = E.loopLog || []).push({ seamF: n.seamF, heardF: n.seamF + runLat(n), Fs: LOOP.Fs, Fe: LOOP.Fe, prevT0F: n.prevT0F, T0F: n.T0F, rate: n.rate }); if (E.loopLog.length > 50) E.loopLog.shift(); E.runs.push({ id: n.id, T0F: n.T0F, startF: n.startF, rate: n.rate, at: E.ctx.currentTime, loop: true }); if (E.runs.length > 50) E.runs.shift(); LOOP.repeats = (LOOP.repeats || 0) + 1; }
  }
  function loopTick(r) {
    if (!loopLive() || !r || r.T0F == null || r.next || !E.playing) return;
    const p = (ctxF() - r.T0F) * r.rate, { Fs, Fe } = LOOP;
    if (p >= Fe || p < Fs - E.SR * 0.05 && r.startF >= Fe) return; // past the range (sought out of it): plays on
    const seam = r.T0F + Fe / r.rate; // context frame where the old run reaches Fe
    if (seam - ctxF() > 2 * E.SR) return; // set up the repeat ~2 s ahead
    const ca = chunkAt(Fs), cb = Math.min(E.song.chunks - 1, ca + 1), ch = E.chunks.get(ca);
    if (!ch || !ch.ready) { loadChunk(ca).then(tick, () => {}); if (cb !== ca) loadChunk(cb).catch(() => {}); return; }
    const SR = E.SR, X = Math.round(LOOP.X * SR), bpm = (HV.A && HV.A.bpm) || 100, beats = (HV.A && parseInt(HV.A.meter, 10)) || 4;
    const gap = LOOP.count ? Math.round(beats * 60 / bpm / r.rate * SR) : 0;
    const n = { id: ++E.runSeq, startF: Math.max(0, Fs - Math.round(X * r.rate)), rate: r.rate, sources: new Set(), scheduled: new Set(),
      T0F: seam + gap - Fs / r.rate, seamF: seam + gap, kind: r.kind, pD: r.pD, dD: r.dD, latD: r.latD, pA: r.pA, pT: r.pT, latA: r.latA, latT: r.latT, dA: r.dA, dT: r.dT, latAm: r.latAm, latTm: r.latTm, genA: r.genA, genT: r.genT, semi: r.semi,
      prevT0F: r.T0F, loop: true };
    // cross-fade: old 1 -> 0 over [seam − X, seam + X] (with a count-in: before the gap); new 0 -> 1 around its start
    const t = (f) => f / SR, oA = gap ? seam - 2 * X : seam - X, oB = gap ? seam : seam + X, nA = n.seamF - X, nB = n.seamF + X;
    (r.g || []).forEach((g) => { if (!g) return; g.gain.setValueAtTime(1, t(oA)); g.gain.linearRampToValueAtTime(0, t(oB)); });
    r.sources.forEach((src) => { try { src.stop(t(oB) + 0.002); } catch (e) { /* not started */ } });
    r.stopAt = oB;
    n.gainStart = 0; n.ramp = (prm) => { prm.setValueAtTime(0, t(nA)); prm.linearRampToValueAtTime(1, t(nB)); };
    r.next = n;
    for (let k = ca; k <= cb; k++) { const c = E.chunks.get(k); if (c && c.ready) schedule(n, k, Math.max(n.startF, k ? k * E.Lf - E.Xf : 0)); }
    if (gap) { // one bar of count-in clicks, heard in the gap (clicks skip the shifter: placed at the heard times)
      const lat = runLat(r), beat = 60 / bpm / r.rate, hi = REC.clickBuf(1500, 30, 0.6), lo = REC.clickBuf(1000, 30, 0.45); n.clicks = [];
      for (let i = 0; i < beats; i++) { const s0 = E.ctx.createBufferSource(); s0.buffer = i ? lo : hi; s0.connect(E.lim); s0.start((seam + lat) / SR + i * beat); n.clicks.push(s0); }
    }
  }


  async function startAt(f, minGo) { // minGo: earliest context time to start (record count-in)
    const r = { id: ++E.runSeq, T0F: null, startF: f, rate: E.rate, sources: new Set(), scheduled: new Set() };
    E.run = r;
    const ctxReady = E.ctx.state === 'running' ? null : E.ctx.resume(); // inside the tap's gesture
    const c = chunkAt(f);
    try {
      await Promise.all([loadChunk(c), c + 1 < E.song.chunks ? loadChunk(c + 1) : null, ctxReady]);
    } catch (e) { if (E.run === r) { failed(); } return; }
    if (E.run !== r || !E.playing) return;
    r.rate = E.rate; // (v0.7.1) the tempo as it is when the run starts: a tempo tap while it was loading counts too
    // (v0.5.3) pitch factors: stems p_A = 2^(s/12)/r; take channel p_T = 2^((s − s_take)/12)/r
    const semi = E.semi || 0, sT = REC.active ? REC.active.transpose || 0 : 0;
    r.semi = semi; r.pA = Math.pow(2, semi / 12) / r.rate; r.pT = Math.pow(2, (semi - sT) / 12) / r.rate;
    if (Math.abs(r.pA - 1) < 1e-9) r.pA = 1; if (Math.abs(r.pT - 1) < 1e-9) r.pT = 1;
    if (r.pA !== 1 || r.pT !== 1) {
      if (!(await E.stretchReady)) { r.rate = 1; r.pA = r.pT = 1; r.semi = 0; } // no AudioWorklet: plain playback
      if (E.run !== r || !E.playing) return;
    }
    const hasT = E.stems.some((st) => st.fx); // a take channel exists
    r.kind = semi || (hasT && sT) ? 'pv' : 'wsola'; // a transpose anywhere: both paths use the phase vocoder (same delay type)
    // (v0.5.3) drums are not transposed: with a transpose they take their own path, p_D = 1 / r (tempo only), same delay
    r.pD = semi && E.stems.some((st) => st.id === 'drums') ? 1 / r.rate : null; if (r.pD != null && Math.abs(r.pD - 1) < 1e-9) r.pD = 1;
    r.latA = latOf(r.pA, r.kind); r.latT = hasT ? latOf(r.pT, r.kind) : 0; r.latD = r.pD != null ? latOf(r.pD, r.kind) : 0;
    const Lmax = Math.max(r.latA, r.latT, r.latD); r.dA = Lmax - r.latA; r.dT = hasT ? Lmax - r.latT : 0; r.dD = r.pD != null ? Lmax - r.latD : 0;
    // switch the bus route only once the previous run's fade-out has reached silence
    const wait = (E.quietAt || 0) - E.ctx.currentTime;
    if (wait > 0) { await new Promise((res) => setTimeout(res, wait * 1000 + 5)); if (E.run !== r || !E.playing) return; }
    route(r);
    E.stems.forEach((st) => { if (st.fx) st.fx.setRate(r.rate); }); // echo = one beat at this tempo
    E.shGen = (E.shGen || 0) + 1; r.genA = E.shGen; r.genT = E.shGen + 0.5; // (stale reports of an earlier run are ignored)
    const shA = r.kind === 'pv' ? E.pvA : E.stretch, shT = r.kind === 'pv' ? E.pvT : E.stretchT;
    if (r.pA !== 1) shA.port.postMessage({ p: r.pA, gen: r.genA }); // fresh shifter state
    if (r.pT !== 1 && hasT) shT.port.postMessage({ p: r.pT, gen: r.genT });
    if (r.pD != null && r.pD !== 1) E.pvD.port.postMessage({ p: r.pD, gen: null });
    const go = Math.max(E.ctx.currentTime + LEAD, (E.quietAt || 0) + 0.005, minGo || 0); // after any fade-out has reached 0
    r.T0F = Math.round(go * E.SR) - f / r.rate;
    E.runs.push({ id: r.id, T0F: r.T0F, startF: f, rate: r.rate, at: E.ctx.currentTime });
    if (E.runs.length > 50) E.runs.shift();
    const g = E.out.gain, t0 = go + runLat(r) / E.SR; // fade in when the first sound leaves the shifter
    hold(g, E.ctx.currentTime); g.setValueAtTime(0, t0); g.setTargetAtTime(1, t0, FADE_TC);
    tick();
  }

  function play() {
    if (!E.song || E.playing) return;
    if (E.released) revive();
    E.playing = true;
    clearTimeout(E.suspendTimer);
    const r = E.run;
    if (r && r.T0F != null) { // paused run still on the frozen clock: resume it exactly where it stopped
      const go = () => { const g = E.out.gain, now = E.ctx.currentTime; hold(g, now); g.setTargetAtTime(1, now, FADE_TC); tick(); };
      if (E.ctx.state === 'running') go(); else E.ctx.resume().then(go, go);
    } else {
      if (E.pausedF >= E.durF) E.pausedF = 0;
      startAt(E.pausedF);
    }
    ui.state(); idleCheck();
  }

  function pause() {
    if (PKS && PK.want.size) setTimeout(() => PK.compactIdle(), 2500); // (v0.6.0) a waiting compaction may run now
    if (!E.playing) return;
    if (REC.on) REC.stop();
    E.playing = false;
    E.pausedF = posF();
    fadeOut();
    clearTimeout(E.suspendTimer);
    const ctx = E.ctx;
    E.suspendTimer = setTimeout(() => { if (!E.playing && E.ctx === ctx) ctx.suspend().then(() => { if (!E.playing && E.ctx === ctx && !E.released) E.pausedF = posF(); }); }, FADE_OUT * 1000 + 30);
    ui.state(); idleCheck();
  }

  function seek(sec) {
    if (!E.song) return;
    if (REC.on) REC.stop(); // a seek ends the take (it keeps what was recorded)
    const f = clamp(Math.round(sec * E.SR), 0, Math.max(0, E.durF - 1));
    const old = E.run;
    if (E.playing && old && old.T0F != null) stopRun(old, fadeOut() + 0.002);
    else stopRun(old, 0);
    E.run = null;
    E.pausedF = f;
    HV.jump = true; // the chord strip re-lays out instantly on a seek (no slide)
    const c = chunkAt(f);
    evict(c, Math.min(E.song.chunks - 1, c + LOOKAHEAD)); // drop the old window now, not after the new one decodes
    if (E.playing) startAt(f); else tick(); // paused: pre-decode around the new spot
    ui.position(true);
    ui.media(true);
  }

  // (v0.7.1) ⏹️: stop and go back to the start — the loop's start while the loop is on. While recording it ends the take
  // exactly like the stop-recording action (the take is saved, never discarded). ⏸ stays pause-in-place.
  function stopToStart() {
    if (!E.song || REC.busy || REC.asking) return;
    if (PKS && PK.want.size) setTimeout(() => PK.compactIdle(), 2500); // (as pause: a waiting compaction may run now)
    if (REC.on) REC.stop();
    const to = LOOP.on && LOOP.Fe > LOOP.Fs ? LOOP.Fs : 0, old = E.run;
    if (E.playing) {
      E.playing = false;
      if (old && old.T0F != null) stopRun(old, fadeOut() + 0.002); else stopRun(old, 0);
      clearTimeout(E.suspendTimer); const ctx = E.ctx;
      E.suspendTimer = setTimeout(() => { if (!E.playing && E.ctx === ctx) ctx.suspend(); }, FADE_OUT * 1000 + 30);
    } else stopRun(old, 0);
    E.run = null; E.pausedF = to;
    HV.jump = true; // the chord strip re-lays out at the start
    const c = chunkAt(to); evict(c, Math.min(E.song.chunks - 1, c + LOOKAHEAD)); tick();
    ui.state(); ui.position(true); ui.media(true); idleCheck();
    lyView(to / E.SR); // 📜 / 🎯 to the start
    if (AS.on) { LY.userScrollAt = 0; if (LY.row && LY.row.el) asFollow(); else { const f = $('lyrLines').firstElementChild; if (f) try { f.scrollIntoView({ block: 'center', behavior: 'smooth' }); } catch (e) { f.scrollIntoView(); } } }
  }

  function finish() {
    if (REC.on) REC.stop(); // song end ends the take
    stopRun(E.run, 0);
    E.run = null; E.playing = false; E.pausedF = 0;
    hold(E.out.gain, E.ctx.currentTime); E.out.gain.setValueAtTime(0, E.ctx.currentTime);
    E.ctx.suspend();
    tick(); ui.state(); ui.position(true);
  }

  // ---- background memory release (v0.2.4)
  const RELEASE_MS = 60000;
  const isHidden = () => document.visibilityState === 'hidden' || E.bg;
  function idleCheck() {
    const idle = E.ready && !E.playing && !E.released && isHidden();
    clearTimeout(E.idleTimer);
    if (!idle) { E.idleSince = 0; return; }
    if (!E.idleSince) E.idleSince = Date.now();
    const left = (window.__harmonyReleaseMs || RELEASE_MS) - (Date.now() - E.idleSince);
    if (left <= 0) release(); else E.idleTimer = setTimeout(idleCheck, left + 50);
  }
  function release() {
    if (E.playing || E.released || !E.ctx) return;
    if (REC.on) return;
    REC.closeMic();
    clearTimeout(E.suspendTimer);
    if (E.run) {
      if (E.run.T0F != null) E.pausedF = posF(); // the frozen clock still says where the pause happened
      stopRun(E.run, 0); E.run.sources.clear(); E.run = null;
    }
    const bytes = E.bytes;
    evict(1, 0); // empty range: drops every chunk (in-flight decodes are discarded when they land)
    E.released = true; E.releases++; E.idleSince = 0;
    E.relLog = { at: Date.now(), bytes, posSec: E.pausedF / E.SR };
    HV.run = null;
    const old = E.ctx;
    try { old.close().catch(() => {}); } catch (e) { /* already closed */ }
  }
  // fresh context + graph, synchronously inside play() (the tap's gesture); startAt() then resumes and decodes
  function revive() {
    E.released = false;
    E.ctx = makeCtx();
    if (E.ctx.sampleRate !== E.SR) { // (not expected: same request, same device) keep the position and frame maths
      const k = E.ctx.sampleRate / E.SR;
      E.pausedF = Math.round(E.pausedF * k); E.D = Math.round(E.D * k); E.SR = E.ctx.sampleRate; frames();
      Object.keys(latCache).forEach((key) => { delete latCache[key]; });
    }
    E.routed = null; E.quietAt = 0; E.stretch = null; E.stretchT = null; E.pvA = null; E.pvT = null; E.pvD = null; REC.mod = null; // (worklet modules are per context)
    buildGraph();
    applyGains(0);
  }

  function failed() {
    E.playing = false; E.run = null;
    ui.status('לא הצלחתי לטעון את השיר. כדאי לנסות שוב.');
    ui.state();
  }

  // ---------------------------------------------------------------- mix
  // vol in percent (0..150); gain = (vol/100)^2 — a gentle loudness-like curve: 50 % ≈ −12 dB, 150 % ≈ +7 dB.
  const mix = { vol: {}, mute: {}, solo: null, tempo: 100, semi: 0 };
  const MIX_KEY = () => 'harmony.mix.v1.' + E.song.id;
  const curve = (v) => Math.pow(v / 100, 2);
  function audible(id) { return mix.solo ? mix.solo === id : !mix.mute[id]; }
  function applyGains(tc) {
    if (!E.ctx || E.released) return; // released: the next play's fresh graph gets the gains
    const now = E.ctx.currentTime;
    E.stems.forEach((s) => {
      const target = audible(s.id) ? curve(mix.vol[s.id]) : 0;
      if (!tc) { s.gain.gain.value = target; return; } // boot: nothing playing yet, set directly
      hold(s.gain.gain, now);
      s.gain.gain.setTargetAtTime(target, now, tc);
    });
  }
  let saveTimer = 0;
  function saveMix(now) {
    clearTimeout(saveTimer);
    const w = () => store.set(MIX_KEY(), { vol: mix.vol, mute: mix.mute, solo: mix.solo, tempo: mix.tempo, semi: mix.semi });
    if (now) w(); else saveTimer = setTimeout(w, 300);
  }
  function loadMix() {
    const m = store.get(MIX_KEY()) || {};
    // a song that gained a lead-guitar stem (v0.2.6): a mix saved before has no "lead" — the old guitar setting
    // covers both guitar channels (volume + mute; a guitar solo becomes "only the two guitars")
    const has = (id) => E.song.stems.some((s) => s.id === id);
    const old = has('lead') && m.vol && m.vol.guitar != null && m.vol.lead == null;
    const src = (id) => (old && id === 'lead' ? 'guitar' : id);
    E.song.stems.forEach((s) => {
      const v = m.vol && +m.vol[src(s.id)];
      mix.vol[s.id] = Number.isFinite(v) ? clamp(Math.round(v), 0, VOL_MAX) : 100;
      mix.mute[s.id] = !!(m.mute && m.mute[src(s.id)]);
    });
    mix.solo = m.solo && has(m.solo) ? m.solo : null;
    if (old && m.solo === 'guitar') { mix.solo = null; E.song.stems.forEach((s) => { mix.mute[s.id] = s.id !== 'guitar' && s.id !== 'lead'; }); }
    const tp = +m.tempo; mix.tempo = Number.isFinite(tp) ? clamp(Math.round(tp / 5) * 5, 50, 150) : 100;
    E.rate = mix.tempo / 100;
    const sm = +m.semi; mix.semi = Number.isFinite(sm) ? clamp(Math.round(sm), -6, 6) : 0; E.semi = mix.semi; // (v0.5.3)
  }
  const act = {
    toggleMute(id) { mix.solo = null; mix.mute[id] = !mix.mute[id]; },
    toggleSolo(id) { mix.solo = mix.solo === id ? null : id; },
    volume(id, v) { mix.vol[id] = clamp(Math.round(v), 0, VOL_MAX); },
    reset() { mix.solo = null; E.song.stems.forEach((s) => { mix.vol[s.id] = 100; mix.mute[s.id] = false; }); },
    noVocals() { mix.solo = null; E.song.stems.forEach((s) => { mix.mute[s.id] = s.id === 'vocals'; }); },
    onlyVocals() { mix.solo = null; E.song.stems.forEach((s) => { mix.mute[s.id] = s.id !== 'vocals'; }); },
  };
  function doMix(name, ...args) {
    act[name](...args);
    applyGains(name === 'volume' ? SLIDE_TC : GAIN_TC);
    saveMix(name !== 'volume');
    ui.mix();
  }

  // tempo: 50..150 % in 5 % steps. Playing -> restart at the same song position at the new rate (a seek-like fade);
  // paused -> drop the frozen run, the next play starts at the new rate.
  function setTempo(pct) {
    pct = clamp(Math.round(pct / 5) * 5, 50, 150);
    if (pct === mix.tempo) return;
    mix.tempo = pct; E.rate = pct / 100; saveMix(true);
    if (E.run && E.run.T0F != null) {
      const at = posF() / E.SR;
      if (E.playing) seek(at); else { stopRun(E.run, 0); E.run = null; E.pausedF = Math.round(at * E.SR); }
    }
    ui.tempo(); ui.media(true);
  }
  // (v0.5.3) key change: −6..+6 semitones, per song; like the tempo, a change restarts at the same spot
  function setSemi(v) {
    v = clamp(Math.round(v), -6, 6);
    if (v === mix.semi || REC.on) return;
    mix.semi = v; E.semi = v; saveMix(true);
    if (E.run && E.run.T0F != null) {
      const at = posF() / E.SR;
      if (E.playing) seek(at); else { stopRun(E.run, 0); E.run = null; E.pausedF = Math.round(at * E.SR); }
    }
    ui.transp(); harmView(audibleSec(), true); lyRetranspose(); pvUpdate();
  }

  // ---------------------------------------------------------------- touch safety (Shaket v0.9 pattern)
  // tapGuard: a click whose touch moved > 10 px or was taken over by a scroll is swallowed before any handler sees it.
  // scrollSafeRange: the native slider never receives the finger; a clearly horizontal drag moves it, a vertical
  // gesture scrolls the page and leaves the value untouched.
  const TAP_SLOP = 10;
  (function tapGuard() {
    const g = { id: null, x: 0, y: 0, bad: false, upAt: 0 };
    const opt = { capture: true, passive: true };
    document.addEventListener('pointerdown', (e) => { g.id = e.pointerId; g.x = e.clientX; g.y = e.clientY; g.bad = false; }, opt);
    document.addEventListener('pointermove', (e) => {
      if (e.pointerId === g.id && Math.hypot(e.clientX - g.x, e.clientY - g.y) > TAP_SLOP) g.bad = true;
    }, opt);
    const end = (bad) => (e) => { if (e.pointerId !== g.id) return; if (bad) g.bad = true; g.id = null; g.upAt = Date.now(); };
    document.addEventListener('pointerup', end(false), opt);
    document.addEventListener('pointercancel', end(true), opt);
    window.addEventListener('scroll', () => { if (g.id !== null) g.bad = true; }, opt);
    document.addEventListener('click', (e) => {
      if (g.bad && Date.now() - g.upAt < 1000) { e.preventDefault(); e.stopImmediatePropagation(); }
      g.bad = false;
    }, true);
  })();
  function scrollSafeRange(r, cls) {
    const w = el('div', 'range-wrap' + (cls ? ' ' + cls : ''));
    if (r.parentNode) r.parentNode.insertBefore(w, r);
    w.append(r);
    let st = null;
    const setFromX = (x) => {
      const box = r.getBoundingClientRect(), th = 12;
      const min = +r.min || 0, max = +r.max || 1, step = +r.step || 1;
      const f = clamp((x - box.left - th) / Math.max(1, box.width - 2 * th), 0, 1);
      const v = Math.round((min + f * (max - min)) / step) * step;
      if (Math.abs(v - +r.value) < step / 2) return;
      r.value = v;
      st.moved = true;
      r.dispatchEvent(new Event('input', { bubbles: true }));
    };
    const done = () => { if (st && st.moved) r.dispatchEvent(new Event('change', { bubbles: true })); st = null; };
    w.addEventListener('pointerdown', (e) => {
      if (e.button > 0) return;
      st = { id: e.pointerId, x: e.clientX, y: e.clientY, sy: window.scrollY, h: false, mouse: e.pointerType === 'mouse', moved: false };
      if (st.mouse) e.preventDefault();
    });
    w.addEventListener('pointermove', (e) => {
      if (!st || e.pointerId !== st.id) return;
      if (!st.h) {
        const dx = Math.abs(e.clientX - st.x), dy = Math.abs(e.clientY - st.y);
        if (window.scrollY !== st.sy) { st = null; return; }
        if (dx > TAP_SLOP && dx > 1.5 * dy) {
          st.h = true;
          try { w.setPointerCapture(e.pointerId); } catch (err) { /* noop */ }
        } else { if (dy > TAP_SLOP) st = null; return; }
      }
      setFromX(e.clientX);
    });
    w.addEventListener('touchmove', (e) => { if (st && st.h && e.cancelable) e.preventDefault(); }, { passive: false });
    w.addEventListener('pointerup', (e) => {
      if (!st || e.pointerId !== st.id) return;
      if (!st.h && st.mouse && Math.hypot(e.clientX - st.x, e.clientY - st.y) <= 4) setFromX(e.clientX);
      done();
    });
    w.addEventListener('pointercancel', () => done());
    return w;
  }
  const fill = (r) => r.style.setProperty('--p', ((r.value - r.min) / (r.max - r.min) * 100) + '%');

  // ---------------------------------------------------------------- UI
  const rows = {};
  let seeking = false, lastMedia = 0;
  const ui = {
    addRow(s) { // one mixer channel (also the record-along channel when the first take arrives)
      const box = $('channels');
      const row = el('div', 'ch' + (s.take ? ' mine' : '')); row.dataset.id = s.id;
      const mute = el('button', 'mute'); mute.type = 'button';
      const head = el('div', 'ch-head');
      const name = el('span', 'ch-name', s.label);
      const meter = el('span', 'ch-meter'); meter.setAttribute('aria-hidden', 'true'); const bar = el('i'); meter.append(bar);
      const val = el('span', 'ch-val');
      const solo = el('button', 'solo', 'רק זה'); solo.type = 'button';
      solo.setAttribute('aria-label', 'רק ' + s.label);
      head.append(name, meter, val, solo);
      const r = el('input'); Object.assign(r, { type: 'range', min: 0, max: VOL_MAX, step: 1 });
      r.setAttribute('aria-label', 'עוצמת ' + s.label);
      row.append(mute, head, r);
      box.append(row);
      scrollSafeRange(r, 'ch-range');
      mute.addEventListener('click', () => doMix('toggleMute', s.id));
      solo.addEventListener('click', () => doMix('toggleSolo', s.id));
      r.addEventListener('input', () => doMix('volume', s.id, +r.value));
      rows[s.id] = { row, mute, solo, r, val, bar };
      if (s.take) REC.fxUi(row); // (v0.4.6) effects of the record-along channel
    },
    build() {
      $('title').textContent = E.song.title;
      $('artist').textContent = E.song.artist;
      document.title = E.song.title + ' · הרמוניה';
      const box = $('channels');
      E.song.stems.forEach((s) => ui.addRow(s));
      $('reset').addEventListener('click', () => doMix('reset'));
      $('presetNoVocals').addEventListener('click', () => doMix('noVocals'));
      $('presetOnlyVocals').addEventListener('click', () => doMix('onlyVocals'));
      if (!E.song.stems.some((s) => s.id === 'vocals')) $('presetNoVocals').hidden = $('presetOnlyVocals').hidden = true; // (v0.11.0) "only vocals" would mute everything
      $('play').addEventListener('click', () => (E.playing ? pause() : play()));
      $('miniPlay').addEventListener('click', () => (E.playing ? pause() : play()));
      $('miniStop').addEventListener('click', stopToStart); // (v0.7.1)
      [['prev', -1], ['next', 1], ['miniPrev', -1], ['miniNext', 1]].forEach(([id, d]) => $(id).addEventListener('click', () => skip(d)));
      REC.ui();
      miniInit();
      const sk = $('seek');
      scrollSafeRange(sk, 'seek-range');
      sk.max = Math.max(1, Math.floor(E.durF / E.SR * 10)); // 0.1 s steps
      sk.addEventListener('input', () => { seeking = true; fill(sk); $('elapsed').textContent = fmt(sk.value / 10); });
      sk.addEventListener('change', () => { seeking = false; seek(sk.value / 10); });
      $('total').textContent = fmt(E.durF / E.SR);
      $('tSlow').addEventListener('click', () => setTempo(mix.tempo - 5));
      $('tFast').addEventListener('click', () => setTempo(mix.tempo + 5));
      $('tReset').addEventListener('click', () => setTempo(100));
      $('sDown').addEventListener('click', () => setSemi(mix.semi - 1));
      $('sUp').addEventListener('click', () => setSemi(mix.semi + 1));
      $('sReset').addEventListener('click', () => setSemi(0));
      E.stretchReady.then((ok) => { $('tempo').hidden = !ok; $('transp').hidden = !ok; });
      ui.mix(); ui.position(true); ui.tempo(); ui.transp();
    },
    mix() {
      E.song.stems.forEach((s) => {
        const o = rows[s.id], on = !mix.mute[s.id], v = mix.vol[s.id];
        o.row.classList.toggle('muted', !on);
        o.row.classList.toggle('solo-on', mix.solo === s.id);
        o.row.classList.toggle('silent', !audible(s.id));
        o.mute.textContent = on ? '🔊' : '🔇';
        o.mute.setAttribute('aria-pressed', String(!on));
        o.mute.setAttribute('aria-label', (on ? 'השתקת ' : 'החזרת ') + s.label);
        o.solo.setAttribute('aria-pressed', String(mix.solo === s.id));
        if (+o.r.value !== v) o.r.value = v;
        fill(o.r);
        o.val.textContent = v + '%';
      });
      const only = (pred) => !mix.solo && E.song.stems.every((s) => !mix.mute[s.id] === pred(s.id));
      $('presetNoVocals').classList.toggle('on', only((id) => id !== 'vocals'));
      $('presetOnlyVocals').classList.toggle('on', only((id) => id === 'vocals'));
    },
    state() {
      document.body.classList.toggle('playing', E.playing);
      ['play', 'miniPlay'].forEach((id) => $(id).setAttribute('aria-label', E.playing ? 'השהיה' : 'ניגון'));
      if (navigator.mediaSession) try { navigator.mediaSession.playbackState = E.playing ? 'playing' : 'paused'; } catch (e) { /* noop */ }
      if (ANDROID) try { window.Android.setState(E.playing); } catch (e) { /* old bridge */ }
      ui.media(true);
    },
    position(force) {
      const sec = posF() / E.SR, sk = $('seek');
      if (!seeking || force) {
        if (!seeking) { sk.value = Math.round(sec * 10); fill(sk); }
        $('elapsed').textContent = fmt(seeking ? sk.value / 10 : sec);
      }
    },
    meters() {
      E.stems.forEach((s) => {
        let l = 0;
        if (E.playing) {
          s.analyser.getFloatTimeDomainData(s.buf);
          let sum = 0; for (let i = 0; i < s.buf.length; i++) sum += s.buf[i] * s.buf[i];
          const db = 20 * Math.log10(Math.sqrt(sum / s.buf.length) + 1e-9);
          l = clamp((db + 54) / 48, 0, 1);
        }
        s.level = Math.max(l, s.level * 0.85); // quick attack, gentle fall
        rows[s.id].bar.style.transform = `scaleX(${s.level.toFixed(3)})`;
      });
    },
    // notification / lock screen: title, artist, elapsed / total
    media(force) {
      const t = Date.now();
      if (!force && t - lastMedia < 5000) return;
      lastMedia = t;
      const dur = E.durF / E.SR, pos = posF() / E.SR;
      if (navigator.mediaSession && navigator.mediaSession.setPositionState) {
        try { navigator.mediaSession.setPositionState({ duration: dur, position: Math.min(pos, dur), playbackRate: E.rate }); } catch (e) { /* noop */ }
      }
      if (ANDROID) try { window.Android.setNow(E.song.title, E.song.artist, dur * 1000, pos * 1000); } catch (e) { /* old bridge */ }
    },
    status(s) { $('status').textContent = s || ''; },
    recState() {
      if (PKS) try { window.Android.setRec(!!(REC.on || REC.busy)); } catch (e) { /* older bridge */ } // (v0.6.0) no pack compaction while recording
      const on = REC.on, b = REC.busy || REC.asking, md = REC.mode;
      ['recBtn', 'miniRec'].forEach((id) => { const x = $(id); x.classList.toggle('on', on); x.setAttribute('aria-pressed', String(on)); x.setAttribute('aria-label', on ? 'עצירת ההקלטה' : 'הקלטה'); });
      const mb = $('recMode');
      mb.textContent = md === 'speaker' ? '🔈 מצב רמקול' : md === 'headphones' ? '🎧 מצב אוזניות' : '❔ אוזניות?';
      mb.classList.toggle('warn', md === 'speaker');
      mb.setAttribute('aria-label', 'מצב הקלטה: ' + (md === 'speaker' ? 'רמקול' : md === 'headphones' ? 'אוזניות' : 'לא ידוע'));
      mb.disabled = on || b;
      const cb = $('recCal'); cb.disabled = on || b; cb.textContent = md === 'speaker' ? 'כיול' : 'כיול במחיאות כפיים';
      const nat = REC.engine() === 'native', mc = $('recMic'), ch = nat ? REC.natChoice() : !!(REC.devs && REC.devs.choice);
      mc.hidden = !ch; mc.disabled = on || b;
      if (ch) { const ph = REC.micPref() !== 'headset'; mc.textContent = 'מיקרופון: ' + (ph ? 'טלפון' : 'אוזניות'); mc.setAttribute('aria-label', 'מיקרופון להקלטה: ' + (ph ? 'של הטלפון' : 'של האוזניות')); }
      const ag = $('recAgc'), agOn = REC.agc();
      ag.hidden = nat || md === 'speaker' || !(agOn || REC.low); ag.disabled = on || b;
      ag.classList.toggle('on', agOn); ag.setAttribute('aria-pressed', String(agOn)); ag.textContent = 'הגברה אוטומטית: ' + (agOn ? 'פועלת' : 'כבויה');
      ['tSlow', 'tFast', 'tReset', 'sDown', 'sUp', 'sReset'].forEach((id) => { if (on) $(id).disabled = true; });
      if (!on) { ui.tempo(); ui.transp(); }
      let c = null; try { c = store.get(REC.latKey()); } catch (e) { /* noop */ }
      const mt = md === 'speaker' ? 'השיר יוסר מההקלטה אחרי העצירה (עדיף אוזניות)' : md === 'headphones' ? 'בלי ביטול הד' : '';
      $('recInfo').textContent = [mt, c ? 'כיול: ' + REC.lr(Math.round(c.ms) + ' ms') + (c.src === 'clap' ? ' (מחיאות)' : '') : 'לא בוצע כיול'].filter(Boolean).join(' · ');
      { const rv = $('recVol'), v = md === 'speaker' && REC.engine() === 'native' ? REC.vol() : null, show = !!v && (v.override || v.g < 0.995);
        rv.hidden = !show;
        if (show) { $('recVolText').textContent = v.override ? 'עוצמת השיר: 100% (בלי הנמכה אוטומטית)' : 'עוצמת השיר הונמכה ל-' + REC.pct(v.g); $('recVolBack').textContent = v.override ? 'הנמכה אוטומטית' : 'להחזיר עוצמה'; } }
      REC.engWarn();
    },
    transp() { // (v0.5.3)
      const v = mix.semi, lab = $('sLabel'); if (!lab) return;
      lab.replaceChildren(document.createTextNode('סולם '), bdi(v > 0 ? '+' + v : v < 0 ? '−' + -v : '0'));
      $('sDown').disabled = v <= -6 || REC.on; $('sUp').disabled = v >= 6 || REC.on; $('sReset').disabled = v === 0 || REC.on;
      $('transp').classList.toggle('changed', v !== 0);
    },
    tempo() {
      const A = HV.A, bpm = A && A.bpm ? Math.round(A.bpm) : null, t = mix.tempo;
      const lab = $('tLabel'); lab.replaceChildren(document.createTextNode('קצב ' + t + '%'));
      if (bpm) { lab.append(document.createTextNode(' · ')); lab.append(bdi(t === 100 ? 'BPM ' + bpm : 'BPM ' + bpm + ' → ' + Math.round(bpm * t / 100))); }
      $('tSlow').disabled = t <= 50; $('tFast').disabled = t >= 150; $('tReset').disabled = t === 100;
      $('tempo').classList.toggle('changed', t !== 100);
    },
  };

  // sticky play / pause (v0.2.4): the bar shows exactly while the big button is out of the viewport
  function miniInit() {
    const bar = $('mini'), big = $('play');
    bar.hidden = false; bar.inert = true; bar.setAttribute('aria-hidden', 'true');
    const set = (show) => {
      bar.classList.toggle('show', show); bar.inert = !show; bar.setAttribute('aria-hidden', String(!show));
      document.documentElement.classList.toggle('mini-on', show);
      if (show) document.documentElement.style.setProperty('--mini-h', bar.offsetHeight + 8 + 'px');
    };
    if (!('IntersectionObserver' in window)) { // fallback: compare on scroll
      const chk = () => { const r = big.getBoundingClientRect(); set(r.bottom <= 0 || r.top >= innerHeight); };
      addEventListener('scroll', chk, { passive: true }); addEventListener('resize', chk); chk(); return;
    }
    // the root starts below the bar's own height: once the big button is entirely in the zone the bar covers (or
    // above it), the bar takes over — never a thin sliver of the big button as the only control
    let io = null, h = -1;
    const watch = () => {
      const nh = bar.offsetHeight; if (nh === h) return; h = nh;
      if (io) io.disconnect();
      io = new IntersectionObserver((es) => { const e = es[es.length - 1]; set(!e.isIntersecting); }, { threshold: 0, rootMargin: -h + 'px 0px 0px 0px' });
      io.observe(big);
    };
    watch(); if ('ResizeObserver' in window) new ResizeObserver(watch).observe(bar); else addEventListener('resize', watch); // text zoom / rotation
  }

  function frame() {
    if (E.song && document.visibilityState === 'visible') { ui.position(false); ui.meters(); harmView(audibleSec(), false); }
    requestAnimationFrame(frame);
  }

  function mediaSession() {
    const ms = navigator.mediaSession;
    if (!ms) return;
    try {
      ms.metadata = new MediaMetadata({ title: E.song.title, artist: E.song.artist, album: 'הרמוניה' });
      ms.setActionHandler('play', () => play());
      ms.setActionHandler('pause', () => pause());
      ms.setActionHandler('stop', () => pause());
      ms.setActionHandler('seekto', (d) => { if (d && Number.isFinite(d.seekTime)) seek(d.seekTime); });
      ms.setActionHandler('seekbackward', (d) => seek(posF() / E.SR - ((d && d.seekOffset) || 10)));
      ms.setActionHandler('seekforward', (d) => seek(posF() / E.SR + ((d && d.seekOffset) || 10)));
    } catch (e) { /* partial support */ }
  }

  // ---------------------------------------------------------------- key / chords / beat (v0.2)
  // analysis.json is made offline (tools/analyze-song.sh): key sections, BPM, meter, beats, downbeats, chords — all in
  // song seconds. The view reads the AUDIBLE song position (the context time leaving the speaker, from
  // getOutputTimestamp, minus the run's anchor T0F — the same anchor every stem source is scheduled from), so the
  // chord strip and the beat dot can't drift from the stems and land on the first animation frame after the sound.
  const SOLF = { C: 'דו', D: 'רה', E: 'מי', F: 'פה', G: 'סול', A: 'לה', B: 'סי' };
  const keySym = (k, mode) => k + (mode === 'minor' ? 'm' : '');
  const keyHe = (k, mode) => SOLF[k[0]] + (k[1] === 'b' ? ' במול' : k[1] === '#' ? ' דיאז' : '') + (mode === 'minor' ? ' מינור' : ' מז׳ור');
  const bdi = (text) => { const b = el('bdi', null, text); b.dir = 'ltr'; return b; };
  // (v0.5.3) transpose: chord / key names move by E.semi; spelling follows the transposed key section (flats in flat
  // keys: F Bb Eb Ab Db Gb major and their relative minors; sharps in sharp keys; C / Am: flats except F#)
  const PC = { C: 0, D: 2, E: 4, F: 5, G: 7, A: 9, B: 11 }, NSH = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B'], NFL = ['C', 'Db', 'D', 'Eb', 'E', 'F', 'Gb', 'G', 'Ab', 'A', 'Bb', 'B'];
  const KMAJ = ['C', 'Db', 'D', 'Eb', 'E', 'F', 'F#', 'G', 'Ab', 'A', 'Bb', 'B'], KMIN = ['C', 'C#', 'D', 'Eb', 'E', 'F', 'F#', 'G', 'G#', 'A', 'Bb', 'B'];
  const pcOf = (n) => (PC[n[0]] + (n[1] === '#' ? 1 : n[1] === 'b' ? -1 : 0) + 12) % 12;
  function trKey(k, mode, s) { const pc = (pcOf(k) + s + 120) % 12; return { key: (mode === 'minor' ? KMIN : KMAJ)[pc], mode, pc }; }
  function spellOf(k, mode) { const maj = mode === 'minor' ? (k.pc + 3) % 12 : k.pc; return [5, 10, 3, 8, 1, 6].includes(maj) ? 'flat' : [7, 2, 9, 4, 11].includes(maj) ? 'sharp' : 'neutral'; }
  function trName(n, s, sp) { const pc = (pcOf(n) + s + 120) % 12; return sp === 'sharp' ? NSH[pc] : sp === 'flat' ? NFL[pc] : pc === 6 ? 'F#' : NFL[pc]; }
  function trChord(label, t) {
    const s = E.semi || 0; if (!s || !label) return label;
    const m = /^([A-G][#b]?)(.*?)(?:\/([A-G][#b]?))?$/.exec(label); if (!m) return label;
    const A = HV.A, secs = A && A.keySections && A.keySections.length ? A.keySections : A ? [{ t0: 0, key: A.key, mode: A.mode }] : null;
    let sp = 'neutral'; if (secs) { const k0 = secs[Math.max(0, lastLE(secs, t || 0, 't0'))], k = trKey(k0.key, k0.mode, s); sp = spellOf(k, k0.mode); }
    return trName(m[1], s, sp) + m[2] + (m[3] ? '/' + trName(m[3], s, sp) : '');
  }
  const HV = { A: null, beats: null, down: null, ci: -2, ki: -2, lit: '', trace: null, run: null, lastF: 0 };
  function audibleSec() {
    const r = E.run;
    if (!E.playing || !r || r.T0F == null) return posF() / E.SR;
    const now = E.ctx.currentTime;
    let ct = now - (E.ctx.outputLatency || E.ctx.baseLatency || 0);
    try {
      const ts = E.ctx.getOutputTimestamp && E.ctx.getOutputTimestamp();
      // extrapolate the last output timestamp only while the clock runs (a timestamp from before a suspend is stale)
      if (ts && ts.contextTime > 0) ct = ts.contextTime + (E.ctx.state === 'running' ? clamp((performance.now() - ts.performanceTime) / 1000, 0, 0.1) : 0);
    } catch (e) { /* latency estimate stays */ }
    ct = Math.min(ct, now); // nothing is heard before it is rendered
    const hf = ct * E.SR - runLat(r);
    let f;
    if (r.prevT0F != null && hf < r.seamF) f = clamp((hf - r.prevT0F) * r.rate, 0, E.durF); // (v0.5.3 loop) still hearing the previous pass
    else {
      f = clamp((hf - r.T0F) * r.rate, r.startF, E.durF);
      if (r.prevT0F != null && !r.seamSeen) { r.seamSeen = true; HV.lastF = 0; HV.jump = true; } // the jump back is heard now (chord strip re-lays out; 📜 / 🎯 follow the row)
    }
    if (HV.run === r) f = Math.max(f, HV.lastF); // monotonic within a run: no back-and-forth from timestamp jitter
    HV.run = r; HV.lastF = f;
    return f / E.SR;
  }
  const lastLE = (arr, t, key) => { // index of the last element with key <= t (binary search), -1 if none
    let lo = 0, hi = arr.length - 1, ans = -1;
    while (lo <= hi) { const m = (lo + hi) >> 1; if ((key ? arr[m][key] : arr[m]) <= t) { ans = m; lo = m + 1; } else hi = m - 1; }
    return ans;
  };
  function harmInit(A) {
    if (!A || !Array.isArray(A.chords) || !Array.isArray(A.beats)) return;
    HV.A = A;
    HV.beats = A.beats;
    const ds = new Set(A.downbeats.map((t) => Math.round(t * 1000)));
    HV.down = A.beats.map((t) => ds.has(Math.round(t * 1000)));
    $('tempoLine').replaceChildren(bdi('BPM ' + Math.round(A.bpm) + ' · ' + A.meter));
    ui.tempo();
    $('meta').hidden = false;
    $('harm').hidden = false;
    window.addEventListener('resize', () => { if (HV.A && HV.ci !== -2) stripRender(HV.ci, true); }); // re-fit (rotation / text size)
    $('chords').addEventListener('click', (e) => {
      const b = e.target.closest('.chord');
      if (b && b.dataset.t) seek(+b.dataset.t + 0.001);
    });
    applyDir(); // song.json dir (lyrics, if any, refine it in lyInit)
    harmView(posF() / E.SR, true);
    lyInit();
    const sk = !!(A.phrases && A.phrases.length);
    ['prev', 'next', 'miniPrev', 'miniNext'].forEach((id) => { $(id).disabled = !sk; });
  }
  // Keyed chips (one button per chord index) so a chord keeps its element as it moves centre -> right. FLIP: measure
  // each kept chip before and after the new layout and slide / scale it from where it was (transform only, 260 ms);
  // new chips fade in from the left. A seek / jump re-lays out instantly. Chips that don't fit drop, farthest first.
  const chips = new Map();
  function chipFor(k, slot) {
    const c = HV.A.chords[k];
    let b = chips.get(k);
    if (!b) {
      const lab = trChord(c.label, c.t0);
      b = el('button', 'chord'); b.type = 'button'; b.dataset.t = c.t0; b.append(bdi(lab));
      b.setAttribute('aria-label', lab); chips.set(k, b); b.dataset.fresh = '1';
    }
    b.className = 'chord ' + slot + (c.unsure ? ' unsure' : '');
    b.hidden = false; b.style.transition = 'none'; b.style.transform = '';
    return b;
  }
  function stripRender(ci, jump) {
    const A = HV.A, n = A.chords.length;
    const cur = ci >= 0 ? ci : null, next = ci >= 0 ? ci + 1 : -ci - 1, last = ci >= 0 ? ci - 1 : -ci - 2;
    const first = new Map();
    if (!jump) chips.forEach((b, k) => { if (b.isConnected && !b.hidden) first.set(k, b.getBoundingClientRect()); });
    const keep = new Set();
    const up = []; for (let j = 0; j < 3 && next + j < n; j++) { up.push(chipFor(next + j, 'up' + (j + 1))); keep.add(next + j); }
    const past = []; for (let j = 0; j < 2 && last - j >= 0; j++) { past.push(chipFor(last - j, 'past' + (j + 1))); keep.add(last - j); }
    let now;
    if (cur != null) { now = chipFor(cur, 'now'); keep.add(cur); }
    else { now = el('span', 'chord now gap'); now.append(bdi('–')); }
    chips.forEach((b, k) => { if (!keep.has(k)) { b.remove(); chips.delete(k); } });
    $('chUp').replaceChildren(...up.slice().reverse()); // far .. near (near the centre)
    $('chNow').replaceChildren(now);
    $('chPast').replaceChildren(...past);              // near .. far
    // fit: drop the farthest chips of a side that doesn't fit its column (large text / narrow screens)
    const fit = (zone, list) => {
      const W = zone.clientWidth, gap = 6;
      let used = list.reduce((a, b) => a + b.offsetWidth, 0) + gap * Math.max(0, list.length - 1);
      for (let j = list.length - 1; j >= 0 && used > W + 0.5; j--) { used -= list[j].offsetWidth + (j ? gap : 0); list[j].hidden = true; }
    };
    fit($('chUp'), up); fit($('chPast'), past);
    if (jump) { chips.forEach((b) => { delete b.dataset.fresh; b.classList.remove('enter'); }); return; }
    const moves = [];
    chips.forEach((b, k) => {
      if (b.hidden) return;
      const f = first.get(k);
      if (!f) { if (b.dataset.fresh) b.classList.add('enter'); delete b.dataset.fresh; return; }
      const l = b.getBoundingClientRect();
      const dx = (f.left + f.width / 2) - (l.left + l.width / 2), sc = l.width ? f.width / l.width : 1;
      if (Math.abs(dx) < 0.5 && Math.abs(sc - 1) < 0.01) return;
      b.style.transform = `translateX(${dx.toFixed(1)}px) scale(${sc.toFixed(3)})`; moves.push(b);
    });
    if (!moves.length) return;
    void document.body.offsetWidth; // commit the inverted state, then play to the real layout
    moves.forEach((b) => { b.style.transition = 'transform .26s ease-out, opacity .26s ease-out'; b.style.transform = ''; });
  }
  function harmView(t, force) {
    const A = HV.A;
    if (!A) return;
    // key section
    const secs = A.keySections && A.keySections.length ? A.keySections : [{ t0: 0, key: A.key, mode: A.mode }];
    const ki = Math.max(0, lastLE(secs, t, 't0'));
    if (ki !== HV.ki || force) {
      HV.ki = ki; const k = E.semi ? trKey(secs[ki].key, secs[ki].mode, E.semi) : secs[ki];
      $('keyLine').replaceChildren(bdi(keySym(k.key, k.mode)), document.createTextNode(' · ' + keyHe(k.key, k.mode)));
    }
    // chord strip: the chord sounding now in the centre, the past ones to its right, the coming ones to its left
    let ci = lastLE(A.chords, t, 't0');
    if (ci >= 0 && t >= A.chords[ci].t1) ci = -1 - ci - 1; // in a gap after chord |ci|: nothing sounding
    if (ci !== HV.ci || force) {
      const pos = (c) => (c >= 0 ? c : -c - 1.5); // gap after chord g sits at g + 0.5
      const jump = force || HV.jump || HV.ci === -2 || Math.abs(pos(ci) - pos(HV.ci)) > 1;
      HV.ci = ci; HV.jump = false;
      stripRender(ci, jump);
    }
    // beat dot: lit for 110 ms after each beat, accented on downbeats
    const bi = lastLE(HV.beats, t);
    const lit = E.playing && bi >= 0 && t - HV.beats[bi] < 0.11 ? (HV.down[bi] ? 'down' : 'beat') : '';
    if (lit !== HV.lit) {
      HV.lit = lit;
      const d = $('beat'); d.classList.toggle('on', !!lit); d.classList.toggle('down', lit === 'down');
    }
    if (HV.trace) { HV.trace.push([performance.now(), t, HV.ci, bi, lit]); if (HV.trace.length > 20000) HV.trace.shift(); }
    lyView(t);
    if (HV.lytrace) { HV.lytrace.push([performance.now(), t, LY.cur]); if (HV.lytrace.length > 20000) HV.lytrace.shift(); }
  }

  // ---------------------------------------------------------------- lyrics (v0.2.1)
  // Only text the user pastes is ever shown; it is stored on the device (localStorage, per song) with any manual line
  // starts. Timing: analysis.json carries vocal PHRASE timestamps (energy on the vocals stem, no words). Non-empty
  // lines map to phrases in order by a monotone DP that matches each line's cumulative share of the text (characters)
  // to the cumulative share of sung time at its start:
  //   lines <= phrases: every line starts on a phrase start; the phrases in between merge into the line;
  //   lines >  phrases: every phrase starts a line; extra lines split their phrase in proportion to their length.
  // A line fixed by hand ("השורה מתחילה עכשיו") becomes an anchor; the mapping re-runs between anchors.
  // Automatic lyrics (lane L): the worker may ship lyrics.json (lines + per-line / per-word times aligned to the vocals
  // stem). With no lyrics of the user's own, its lines are shown; each matching line's aligned start is an anchor below
  // the user's pins, and its words light up in turn (verdict "ok" or "weak", line ok and aligned, word count = the line's words; else the
  // line alone). The timing sits beside the text as LY.auto (line hashes, no text) and stays with any line whose text
  // is unchanged; pasted text always wins. No lyric text or source detail is ever logged.
  // (v0.14.0) "🎤 טעינת מילים": a song with no lyrics at all (no own text, no pack lyrics.json) may ask the phone to look
  // its lyrics up by name (title, artist, duration; Android.lyricsLookup, native HTTP). The answer is kept apart from
  // everything else: harmony.lyrics.auto.v1.<id> + the pack's lyrics-lookup.json (never lyrics.json, never the user's
  // text). Synced lines are fitted to the song's phrases by one global offset (lyFit); a failed fit or plain text maps
  // like pasted text. It is always labelled "נמצאו לפי שם השיר · ייתכן שלא תואמות"; "לא תואם? הסתר" keeps its id as
  // rejected (never offered again). Order shown: own text > pack lyrics.json > the lookup > nothing (lyPick).
  const LY = { lines: [], starts: [], fix: {}, fine: {}, text: '', cur: -2, sel: -1, userScrollAt: 0, built: false, pack: null, auto: null, am: [] };
  // "גלילה אוטומטית" (v0.4.7): ON (default) = the page follows the sung line (the only programmatic page scroll in the
  // app is lyView's scrollIntoView below); OFF = playback never moves the page — the lines / chords still update in
  // place. Turning it back on scrolls once to the current line. Remembered on the device.
  const AS = { on: store.get('harmony.autoscroll.v1') !== false };
  function asFollow() { const r = LY.row; if (!r || !r.el || !$('lyrEditor').hidden) return; try { r.el.scrollIntoView({ block: 'center', behavior: 'smooth' }); } catch (e) { r.el.scrollIntoView(); } }
  function asSync() {
    const lab = 'גלילה אוטומטית: ' + (AS.on ? 'פועלת' : 'כבויה'); // the buttons are 📜 only (an emoji, not text)
    ['miniScroll', 'lyrScroll'].forEach((id) => { const b = $(id); if (!b) return; b.classList.toggle('on', AS.on); b.setAttribute('aria-pressed', String(AS.on)); b.setAttribute('aria-label', lab); b.title = lab; });
  }
  // ---- pitch view (v0.4.8): under each lyric row, the ACTIVE take's pitch vs the song's own vocal melody
  // (songs/<id>/melody.json, made offline from the vocal stem: numbers only). The take is analysed once, after it is
  // recorded or when first shown (pitch.js in a Worker), and cached with the take. Per sung line the timing is removed
  // (DTW, as the offline analysis) and each 10 ms of his voice becomes a dot: green within ±50 cents of the melody, red
  // above / below (±300 cents shown), grey where there is no reliable reference (never a fake green / red).
  const PV = { on: store.get('harmony.pitchview.v1') !== false, ref: null, res: null, worker: null, seq: 0, job: null, song: null };
  const PV_V = 2; // (v0.7.0) + the level per frame (dB), and the track it was taken from
  // (v0.7.0) the take's OWN voice: the cleaned track (the song removed) in speaker mode, the raw take otherwise
  const vaSrc = (t) => (t.mode === 'speaker' && t.clean && !t.clean.error ? 'c' : 'a');
  function pvNote(msg) { const n = $('pvNote'); if (n) { n.textContent = msg || ''; n.hidden = !msg; } }
  function pvSync() {
    const b = $('pvToggle'); if (!b) return; const lab = 'תצוגת גובה (איפה מזייפים): ' + (PV.on ? 'פועלת' : 'כבויה');
    b.classList.toggle('on', PV.on); b.setAttribute('aria-pressed', String(PV.on)); b.setAttribute('aria-label', lab); b.title = lab;
    b.hidden = !PV.ref; // a song without a reference melody: nothing to show
  }
  function pvSet(on) { PV.on = !!on; store.set('harmony.pitchview.v1', PV.on); pvSync(); pvUpdate(); }
  async function pvWorker() { // from a Blob of the fetched script: loads the same way as every other asset in the app
    if (!PV.worker) { // (v0.7.0) pitch.js + voice.js in one Worker: the voice analysis runs there too
      const src = (await (await fetch('pitch.js')).text()) + '\n' + (await (await fetch('voice.js')).text());
      PV.worker = new Worker(URL.createObjectURL(new Blob([src], { type: 'application/javascript' })));
    }
    return PV.worker;
  }
  // (v0.7.0) the Worker is closed after PV_IDLE_MS without work: its memory (a 4-min take's track) goes back to the phone
  const PV_IDLE_MS = 15000;
  async function pvRun(msg) {
    const w = await pvWorker();
    PV.busyN = (PV.busyN || 0) + 1; clearTimeout(PV.idleT);
    const idle = () => { PV.busyN--; clearTimeout(PV.idleT); PV.idleT = setTimeout(() => { if (!PV.busyN && PV.worker === w) { w.terminate(); PV.worker = null; PV.closed = (PV.closed || 0) + 1; } }, PV_IDLE_MS); };
    return new Promise((res, rej) => {
      const id = ++PV.seq;
      const on = (e) => { if (!e.data || e.data.id !== id) return; w.removeEventListener('message', on); idle(); if (e.data.error) rej(new Error(e.data.error)); else res(e.data); };
      w.addEventListener('message', on); w.addEventListener('error', (e) => { PV.worker = null; idle(); rej(e); }, { once: true });
      // (v0.7.0) chunks the pack cache still holds are copied, not moved (a moved buffer would leave the cache empty)
      const held = new Set(PK.cache.values()), tr = (msg.chunks || []).filter((c) => !held.has(c[1])).map((c) => c[1].buffer);
      w.postMessage({ id, ...msg }, tr);
    });
  }
  // o (v0.7.0, another song's take): { get(id, k), C, keep: false = don't cache into the phone's record }
  async function pvChunks(t, src, o) { const C = (o && o.C) || E.Lf, get = (o && o.get) || REC.getChunk, id = src === 'c' ? t.id + ':c' : t.id, out = [];
    for (let k = Math.floor(t.startF / C); k * C < t.endF; k++) { const d = await get(id, k); if (d) out.push([k, d]); } return out; }
  function pvTrack(t, o) { // the take's pitch + level, cached with the take (Int16 cents / Int8 dB per 10 ms song frame, -32768 = unvoiced)
    const src = vaSrc(t), P0 = t.pitch;
    if (P0 && P0.v === PV_V && P0.src === src && P0.cents instanceof Int16Array && P0.db instanceof Int8Array) return Promise.resolve(P0); // (a record restored from a pack's take.json carries no usable cache)
    if (PV.job && PV.job.id === t.id && PV.job.src === src) return PV.job.p;
    const note = !o;
    const p = (async () => {
      if (note) pvNote('מנתח גובה…'); const t0 = performance.now(); let r = null, how = 'worker'; const C = (o && o.C) || E.Lf;
      try { r = await pvRun({ chunks: await pvChunks(t, src, o), C, startF: t.startF, endF: t.endF }); } catch (e) { r = null; }
      if (!r) { how = 'main'; await new Promise((q) => setTimeout(q, 30)); r = window.HarmonyPitch.trackTake(await pvChunks(t, src, o), C, t.startF, t.endF); }
      const n = r.cents.length, q = new Int16Array(n), db = new Int8Array(n);
      for (let i = 0; i < n; i++) { q[i] = isNaN(r.cents[i]) ? -32768 : Math.round(r.cents[i]); db[i] = r.db ? Math.max(-120, Math.min(0, Math.round(r.db[i]))) : -120; }
      t.pitch = { v: PV_V, src, f0: r.f0, cents: q, db, ms: Math.round(performance.now() - t0), how };
      if (!o || o.keep !== false) REC.op('takes', 'readwrite', (st) => st.put(t), true).catch(() => {}); // a derived cache: quiet (never a pack save)
      if (note) pvNote(''); return t.pitch;
    })();
    PV.job = { id: t.id, src, p }; p.finally(() => { if (PV.job && PV.job.p === p) PV.job = null; });
    return p;
  }
  async function pvUpdate() {
    pvSync();
    const t = REC.active;
    if (!PV.on || !t || !PV.ref || !HV.A || !LY.rows || !LY.lines.length) { pvClear(); return; }
    let p; try { p = await pvTrack(t); } catch (e) { pvNote('ניתוח הגובה נכשל'); return; }
    if (REC.active !== t || !PV.on) return;
    // (v0.5.3) the reference melody in the key the take was sung in: shifted by the take's transpose
    const sT = t.transpose || 0, ref = sT ? (PV.refS && PV.refS.s === sT && PV.refS.base === PV.ref ? PV.refS.ref : (PV.refS = { s: sT, base: PV.ref, ref: { ...PV.ref, cents: PV.ref.cents.map((c) => c + 100 * sT) } }).ref) : PV.ref;
    if (!PV.res || PV.res.take !== t || PV.res.ref !== ref) {
      const cents = new Float32Array(p.cents.length); for (let i = 0; i < cents.length; i++) cents[i] = p.cents[i] === -32768 ? NaN : p.cents[i];
      PV.res = { take: t, ref, ...window.HarmonyPitch.compare({ f0: p.f0, cents }, ref, HV.A.phrases) };
    }
    pvDraw(); pvNote('🎯 ירוק = בטון · אדום = מעל / מתחת לטון · אפור = אין למה להשוות');
  }
  function pvClear() { document.querySelectorAll('#lyrLines .pv').forEach((x) => x.remove()); PV.head = null; if (!PV.job) pvNote(''); }
  const pvEnd = (r) => (r.kind === 'line' ? r.c1 : r.t1);
  function pvDraw() {
    const res = PV.res, t = REC.active; if (!res || !t || res.take !== t || !LY.rows) return;
    const sh = (t.nudgeMs || 0) / 1000, dots = res.dots, dpr = window.devicePixelRatio || 1, ltr = $('lyrLines').getAttribute('dir') === 'ltr';
    $('lyrLines').classList.toggle('pv-ltr', ltr);
    const ta = t.startF / E.SR + sh, tb = t.endF / E.SR + sh; // rows the take doesn't reach get no strip
    LY.rows.forEach((r) => {
      let box = r.el && r.el.querySelector(':scope > .pv');
      if (!r.el || !(pvEnd(r) > r.t0) || !Number.isFinite(r.t0) || pvEnd(r) <= ta || r.t0 >= tb) { if (box) box.remove(); return; }
      if (!box) { box = el('div', 'pv'); box.setAttribute('aria-hidden', 'true'); box.append(el('canvas', 'pv-c'), el('i', 'pv-head'), el('span', 'pv-badge')); r.el.append(box); }
      const cv = box.firstChild, w = Math.max(1, box.clientWidth), h = Math.max(1, box.clientHeight);
      cv.width = Math.round(w * dpr); cv.height = Math.round(h * dpr);
      const g = cv.getContext('2d'); g.setTransform(dpr, 0, 0, dpr, 0, 0); g.clearRect(0, 0, w, h);
      const mid = h / 2, k = (h / 2 - 2) / 300, a = r.t0, b = pvEnd(r);
      g.fillStyle = 'rgba(95, 211, 141, .10)'; g.fillRect(0, mid - 50 * k, w, 100 * k);
      g.fillStyle = 'rgba(255, 255, 255, .22)'; g.fillRect(0, mid - 0.5, w, 1);
      let lo = 0, hi = dots.length; const fa = Math.floor((a - sh) / 0.01); while (lo < hi) { const m = (lo + hi) >> 1; if (dots[m][0] < fa) lo = m + 1; else hi = m; }
      const R = Math.max(1.2, Math.min(2.2, h / 18));
      for (let i = lo; i < dots.length; i++) {
        const tt = dots[i][0] * 0.01 + sh; if (tt > b) break; if (tt < a) continue;
        const c = dots[i][1], fx = ((tt - a) / (b - a)) * w, x = ltr ? fx : w - fx; // time runs the way the chords above it do
        const y = isNaN(c) ? mid : mid - Math.max(-300, Math.min(300, c)) * k;
        g.fillStyle = isNaN(c) ? 'rgba(170, 176, 196, .55)' : Math.abs(c) <= 50 ? '#5fd38d' : '#ff6b6b';
        g.beginPath(); g.arc(x, y, R, 0, 2 * Math.PI); g.fill();
      }
      vaBadge(r); // (v0.7.0) the line's score: the same numbers + colour as the row and the report
    });
    PV.head = null;
  }
  function pvHead(t) { // the playhead on the current row's strip (moved by transform only: no redraw while playing)
    const r = LY.row, box = r && r.el && r.el.querySelector(':scope > .pv');
    if (PV.head && PV.head !== box) PV.head.classList.remove('on');
    if (!box) { PV.head = null; return; }
    const f = Math.max(0, Math.min(1, (t - r.t0) / (pvEnd(r) - r.t0)));
    const hd = box.children[1], ltr = $('lyrLines').classList.contains('pv-ltr'); hd.style.transform = 'translateX(' + ((ltr ? 1 : -1) * f * (box.clientWidth - 2)).toFixed(1) + 'px)';
    if (PV.head !== box) { box.classList.add('on'); PV.head = box; }
  }
  // ---- 🎙️ voice analysis + per-line score (v0.7.0). ON THE PHONE ONLY (voice.js in the pitch Worker): the voice never
  // leaves the phone. Per take: the take's own voice (vaSrc) vs the song's melody (in the take's key), its lines (by
  // number / time, never text) and beats; timed and judged against the song's ORIGINAL singer measured the same way
  // (vaBase: his vocal stem through the same analysis, once per song, kept on the phone). Results: IndexedDB
  // ("voice:<take>") + the song's pack (takes/<take>/analysis.json: derived, recomputable; the take is never touched).
  const VA = { mem: new Map(), base: new Map(), cur: null, job: null, log: [], scope: 'take', tone: null };
  const HVo = () => window.HarmonyVoice;
  const VA_BASE_KEY = (id) => 'harmony.voice.base.v' + HVo().VOICE_V + '.' + id;
  const vaIdb = (tid) => 'voice:' + tid;
  function vaFresh(a, t, base) { // a stored analysis still describes this take as it is now
    return !!(a && HVo() && a.v === HVo().VOICE_V && a.src === vaSrc(t) && (a.nudgeMs || 0) === (t.nudgeMs || 0) && (a.transpose || 0) === (t.transpose || 0)
      && a.base && base && a.base.at === base.at && a.base.src === base.src);
  }
  async function vaLoad(songId, tid, idx) { // memory -> phone -> pack
    if (VA.mem.has(tid)) return VA.mem.get(tid);
    let a = null;
    try { a = await REC.op('tchunks', 'readonly', (st) => st.get(vaIdb(tid))); } catch (e) { a = null; }
    if (!a && PKS) {
      const ix = idx || (E.song && songId === E.song.id ? PK.idx : null);
      if (!ix || (ix.takes && ix.takes[tid] && ix.takes[tid].files && ix.takes[tid].files['analysis.json'])) a = await getJson('songs/' + songId + '/takes/' + tid + '/analysis.json');
    }
    if (a && a.takeId === tid) VA.mem.set(tid, a); else a = null;
    return a;
  }
  async function vaStore(songId, tid, a) {
    VA.mem.set(tid, a);
    try { await REC.op('tchunks', 'readwrite', (st) => st.put(a, vaIdb(tid))); } catch (e) { /* the pack still gets it */ }
    PK.mark(songId, { take: tid, voice: true });
  }
  async function vaRun(inp) { // the analysis in the Worker (main thread only if there is no Worker)
    try { const r = await pvRun({ op: 'voice', inp }); return r.res; } catch (e) { await new Promise((q) => setTimeout(q, 30)); return HVo().analyse(inp); }
  }
  const vaTakeIn = (p) => { const n = p.cents.length, c = new Float32Array(n), d = new Float32Array(n); for (let i = 0; i < n; i++) { c[i] = p.cents[i] === -32768 ? NaN : p.cents[i]; d[i] = p.db[i]; } return { f0: p.f0, cents: c, db: d }; };
  const vaRefIn = (ref, semi) => ({ cents: semi ? ref.cents.map((c) => c + 100 * semi) : ref.cents, conf: ref.conf, minConf: ref.minConf });
  // the song's original singer, measured the same way: his vocal stem decoded chunk by chunk (Int16 on the song timeline)
  async function vaBase(S) { // S: { id, base (url), song (song.json), A (analysis.json), ref }
    if (VA.base.has(S.id)) return VA.base.get(S.id);
    let b = store.get(VA_BASE_KEY(S.id));
    if (!b || !b.at) {
      const t0 = performance.now(); b = null;
      const voc = (S.song.stems || []).find((x) => x.id === 'vocals');
      try {
        if (voc && E.ctx) {
          const r = E.SR / S.song.sampleRate, Lf = Math.round(S.song.chunkFrames * r), Mf = Math.round(S.song.marginFrames * r), N = Math.floor(S.song.frames * r), chunks = [];
          for (let k = 0; k < S.song.chunks; k++) {
            const buf = await decode(await (await fetch(S.base + 'vocals-' + String(k).padStart(2, '0') + '.' + (S.song.ext || 'opus'))).arrayBuffer());
            const ch = buf.numberOfChannels, x0 = buf.getChannelData(0), x1 = ch > 1 ? buf.getChannelData(1) : null, sF = Math.max(0, k * Lf - Mf), d = new Int16Array(Lf);
            for (let f = k * Lf; f < Math.min(N, (k + 1) * Lf); f++) { const i = f - sF + E.D; if (i < 0 || i >= x0.length) continue; const v = x1 ? (x0[i] + x1[i]) / 2 : x0[i]; d[f - k * Lf] = v >= 1 ? 32767 : v <= -1 ? -32768 : Math.round(v * 32767); }
            chunks.push([k, d]); await new Promise((q) => setTimeout(q, 0));
          }
          const tr = await pvRun({ chunks, C: Lf, startF: 0, endF: N });
          const res = await vaRun({ take: { f0: tr.f0, cents: tr.cents, db: tr.db }, ref: vaRefIn(S.ref, 0), phrases: S.A.phrases || [], beats: S.A.beats || [], nudgeMs: 0, meta: { takeId: 'orig', songId: S.id } });
          b = HVo().baseline(res); b.wallMs = Math.round(performance.now() - t0); b.trackMs = tr.ms;
        }
      } catch (e) { b = null; VA.log.push({ at: Date.now(), song: S.id, baseError: String(e && e.message || e) }); }
      if (!b) b = { ...HVo().K.BASE_DEFAULT, v: HVo().VOICE_V, at: 1 }; // no vocal stem: the defaults (measured on the four songs' originals)
      store.set(VA_BASE_KEY(S.id), b);
    }
    VA.base.set(S.id, b);
    return b;
  }
  const vaSongHere = () => ({ id: E.song.id, base: E.base, song: E.song, A: HV.A, ref: PV.ref });
  async function vaAnalyse(t, S, o) { // one take -> its analysis (stored); S: the song (default: this one); o: pvTrack's (another song)
    S = S || vaSongHere();
    const t0 = performance.now(), base = await vaBase(S), p = await pvTrack(t, o), t1 = performance.now();
    const inp = { take: vaTakeIn(p), ref: vaRefIn(S.ref, t.transpose || 0), phrases: S.A.phrases || [], beats: S.A.beats || [], nudgeMs: t.nudgeMs || 0, base,
      meta: { takeId: t.id, songId: S.id, created: t.created, transpose: t.transpose || 0, src: vaSrc(t), mode: t.mode, latSource: t.latSource || (t.calibrated ? 'calibration' : 'estimate') } };
    const a = await vaRun(inp);
    a.name = t.name; a.wallMs = Math.round(performance.now() - t0); a.trackMs = Math.round(t1 - t0);
    VA.log.push({ at: Date.now(), song: S.id, take: t.id, wallMs: a.wallMs, trackMs: a.trackMs, analyseMs: a.ms, takeSec: a.takeSec }); if (VA.log.length > 40) VA.log.shift();
    await vaStore(S.id, t.id, a);
    return a;
  }
  // the active take: its stored analysis if still valid, else analysed now (after a take, a nudge, a cleaning, …)
  async function vaUpdate() {
    const t = REC.active, H = HVo();
    if (!t || !H || !PV.ref || !HV.A || !E.song) { VA.cur = null; vaPaint(); return; }
    if (VA.cur && VA.cur.t !== t) { VA.cur = null; vaPaint(); }
    let a = await vaLoad(E.song.id, t.id);
    const base = VA.base.get(E.song.id) || store.get(VA_BASE_KEY(E.song.id));
    if (REC.active !== t) return;
    if (vaFresh(a, t, base)) { VA.cur = { t, a }; vaPaint(); return; }
    if (VA.job) { VA.again = true; return; }
    if (REC.on || REC.busy) { setTimeout(vaUpdate, 2000); return; }
    VA.job = vaAnalyse(t).then((x) => { if (REC.active === t) { VA.cur = { t, a: x }; vaPaint(); if (!$('vaBox').hidden) vaRender(); } }, (e) => { VA.log.push({ at: Date.now(), error: String(e && e.message || e) }); })
      .finally(() => { VA.job = null; if (VA.again) { VA.again = false; vaUpdate(); } });
  }
  // the rows: each lyric row = the song's lines (phrases) inside it, combined; no lyrics: the song's own lines
  function vaRows() {
    const a = VA.cur && VA.cur.a; if (!a) return [];
    if (LY.lines.length && LY.rows) return LY.rows.filter((r) => r.kind === 'line' && Number.isFinite(r.t0)).map((r) => {
      const ls = a.lines.filter((s) => { const m = (s.t0 + s.t1) / 2; return m >= r.t0 && m < (r.c1 != null ? r.c1 : r.t1); });
      return { i: r.i, num: r.i + 1, t0: r.t0, row: r, lines: ls, score: HVo().combine(ls) };
    });
    return a.lines.map((s) => ({ i: s.n - 1, num: s.n, t0: s.t0, row: null, lines: [s], score: HVo().combine([s]) }));
  }
  const VA_COL_HE = { green: 'ירוק', yellow: 'צהוב', red: 'אדום', grey: 'אפור (לא הושר / אין למה להשוות)' };
  function vaPaint() {
    const rows = vaRows(), byRow = new Map(rows.filter((x) => x.row).map((x) => [x.row, x.score]));
    (LY.rows || []).forEach((r) => {
      if (r.kind !== 'line' || !r.el) return;
      const sc = byRow.get(r) || null; r.score = sc;
      r.el.classList.remove('sc-green', 'sc-yellow', 'sc-red', 'sc-grey');
      if (sc && sc.col !== 'none') { r.el.classList.add('sc-' + sc.col); r.el.setAttribute('aria-description', 'ציון השורה: ' + VA_COL_HE[sc.col]); } else r.el.removeAttribute('aria-description');
      vaBadge(r);
    });
  }
  const vaSigned = (x) => (x > 0 ? '+' : x < 0 ? '−' : '') + Math.abs(x);
  function vaBadge(r) { // the 🎯 strip's badge: the line's median deviation, in the line's colour
    const box = r.el && r.el.querySelector(':scope > .pv'), bd = box && box.lastChild; if (!bd) return;
    const sc = r.kind === 'line' ? r.score : null, ok = sc && sc.col !== 'grey' && sc.col !== 'none' && sc.med != null;
    bd.textContent = ok ? vaSigned(sc.med) : '';
    bd.className = 'pv-badge' + (ok ? ' sc-' + sc.col : '');
  }
  function vaNumbers(sc, num) { // a line's numbers, plain Hebrew (tap a line / the report)
    if (!sc) return '';
    if (sc.col === 'grey') return 'שורה ' + num + ': לא הושרה בהקלטה הזו (או שאין במנגינה למה להשוות)';
    const lean = Math.abs(sc.med) >= 10 ? ' · נוטה ' + REC.lr(vaSigned(sc.med)) + ' סנט' : '';
    const tim = sc.tim != null ? ' · כניסה ' + (Math.abs(sc.tim) < 10 ? 'בזמן' : REC.lr(Math.abs(sc.tim) + ' ms') + (sc.tim > 0 ? ' מאוחר' : ' מוקדם')) : '';
    return 'שורה ' + num + ': ' + sc.pIn + '% בטון (±50 סנט) · סטייה ממוצעת ' + sc.mAbs + ' סנט' + lean + tim;
  }
  // 🎵 a target / reference tone: the note itself, plain (sine + a soft octave), on its own (not through the mix)
  function vaTone(cents, sec) {
    if (!E.ctx || !Number.isFinite(cents)) return;
    if (E.released) revive();
    if (E.ctx.state !== 'running') E.ctx.resume();
    if (VA.tone) { try { VA.tone.stop(); } catch (e) { /* done */ } VA.tone = null; }
    const c = E.ctx, now = c.currentTime + 0.03, d = sec || 1.6, hz = 55 * Math.pow(2, cents / 1200), g = c.createGain(), o1 = c.createOscillator(), o2 = c.createOscillator(), g2 = c.createGain();
    o1.frequency.value = hz; o2.frequency.value = hz * 2; g2.gain.value = 0.18;
    g.gain.setValueAtTime(0, now); g.gain.linearRampToValueAtTime(0.22, now + 0.04); g.gain.setValueAtTime(0.22, now + d - 0.15); g.gain.linearRampToValueAtTime(0, now + d);
    o1.connect(g); o2.connect(g2); g2.connect(g); g.connect(c.destination);
    o1.start(now); o2.start(now); o1.stop(now + d + 0.05); o2.stop(now + d + 0.05);
    VA.tone = { stop: () => { o1.stop(); o2.stop(); } }; VA.lastTone = { hz: Math.round(hz * 10) / 10, sec: d, at: Date.now() };
  }
  function vaFirstNote(s, oct) { // a line's first held note in the key it is played in now, in the octave he sings it
    if (!PV.ref || !s) return NaN;
    const ref = PV.ref, a = Math.floor(s.t0 * 100), b = Math.floor(s.t1 * 100), ok = (j) => j >= 0 && j < ref.cents.length && ref.conf[j] >= ref.minConf && !isNaN(ref.cents[j]);
    for (let j = a; j < b; j++) { if (!ok(j)) continue; let e = j; while (e < b && ok(e)) e++; if (e - j >= 10) { const v = []; for (let q = j + 3; q < Math.min(e, j + 25); q++) v.push(ref.cents[q]); return window.HarmonyPitch.med(v) + 100 * (mix.semi || 0) + 1200 * (oct || 0); } j = e; }
    return NaN;
  }
  // a line to practise: jump there and repeat it (🔁)
  // (v0.7.2) closing the report always gives the page its scrolling back (a line to practise used to hide the report
  // but leave body.va-on — overflow: hidden — so the page could no longer be scrolled: it looked stuck inside the loop)
  function vaHide() { $('vaBox').hidden = true; document.body.classList.remove('va-on'); if (typeof backSync === 'function') backSync(); }
  function vaPractise(x) {
    vaHide();
    if (LY.lines.length || HV.A) loopSet(x.i, x.i, true);
    seek(Math.max(0, x.t0 - 0.12)); if (!E.playing) play();
    ui.status('חזרה על שורה ' + x.num + ' (🔁)');
  }
  // ---- the report (🎙️): this take / all takes of all songs
  const VA_MIN_VOICED_S = 10; // less singing than this (s): the report says so instead of "nothing stands out"
  const VA_MET = [ // the progress charts: one per measure
    { k: 'pIn', name: 'כמה מהשירה בטון', unit: '%', good: 'up' },
    { k: 'bias', name: 'נטייה בגובה (0 = בדיוק)', unit: ' סנט', good: 'zero' },
    { k: 'jitter', name: 'יציבות בצלילים ארוכים (פחות = יציב)', unit: ' סנט', good: 'down' },
    { k: 'scoop', name: 'כניסות מלמטה', unit: '%', good: 'down' },
    { k: 'timing', name: 'תזמון כניסות (0 = כמו המקור)', unit: ' ms', good: 'zero' },
    { k: 'cut', name: 'שורות שנגמרות מוקדם', unit: '%', good: 'down' },
  ];
  function vaChart(series, met) {
    const pts = series.map((s, i) => [i, s[met.k]]).filter((p) => p[1] != null && Number.isFinite(p[1]));
    const wrap = el('div', 'va-chart'), head = el('div', 'va-ch-h');
    head.append(el('span', null, met.name));
    const last = pts.length ? pts[pts.length - 1][1] : null; head.append(bdi(last == null ? '—' : (met.good === 'zero' ? vaSigned(Math.round(last)) : Math.round(last)) + met.unit));
    wrap.append(head);
    if (pts.length < 2) { wrap.append(el('p', 'va-ch-none', pts.length ? 'נקודה אחת — הגרף יופיע אחרי הקלטה נוספת' : 'אין עדיין נתונים')); return wrap; }
    const W = 300, H = 56, P = 6, n = series.length, ys = pts.map((p) => p[1]);
    let lo = Math.min(...ys), hi = Math.max(...ys); if (met.good === 'zero') { lo = Math.min(lo, 0); hi = Math.max(hi, 0); } if (hi - lo < 1) { hi += 1; lo -= 1; }
    const X = (i) => P + (n > 1 ? i / (n - 1) : 0.5) * (W - 2 * P), Y = (v) => H - P - (v - lo) / (hi - lo) * (H - 2 * P);
    const NS = 'http://www.w3.org/2000/svg', svg = document.createElementNS(NS, 'svg'); svg.setAttribute('viewBox', '0 0 ' + W + ' ' + H); svg.setAttribute('class', 'va-svg'); svg.setAttribute('aria-hidden', 'true');
    const mk = (tag, at) => { const e = document.createElementNS(NS, tag); Object.entries(at).forEach(([k, v]) => e.setAttribute(k, v)); svg.append(e); return e; };
    if (met.good === 'zero') mk('line', { x1: P, x2: W - P, y1: Y(0), y2: Y(0), class: 'va-zero' });
    mk('polyline', { points: pts.map((p) => X(p[0]).toFixed(1) + ',' + Y(p[1]).toFixed(1)).join(' '), class: 'va-pl' });
    pts.forEach((p) => mk('circle', { cx: X(p[0]).toFixed(1), cy: Y(p[1]).toFixed(1), r: 2.6, class: 'va-dot' }));
    wrap.append(svg);
    const first = pts[0][1], d = last - first, better = met.good === 'up' ? d > 0 : met.good === 'down' ? d < 0 : Math.abs(last) < Math.abs(first);
    wrap.append(el('p', 'va-ch-trend', Math.abs(d) < 1 ? 'בלי שינוי מההקלטה הראשונה' : (better ? '↗ השתפר מאז ההקלטה הראשונה' : '↘ פחות טוב מההקלטה הראשונה') + ' (' + pts.length + ' הקלטות)'));
    return wrap;
  }
  function vaExercise(id, ctx) {
    const x = HVo().EX[id]; if (!x) return null;
    const box = el('div', 'va-ex'); box.append(el('p', 'va-ex-n', '🏋️ ' + x.name), el('p', 'va-ex-how', x.how), el('p', 'va-ex-why', 'למה: ' + x.why));
    const acts = el('div', 'va-acts');
    if (x.tool === 'tone' && Number.isFinite(ctx.tone)) { const b = el('button', 'chip', '🎵 צליל מטרה'); b.type = 'button'; b.addEventListener('click', () => vaTone(ctx.tone, id === 'longTones' ? 6 : 1.6)); acts.append(b); }
    if (x.tool === 'loop' && ctx.line) { const b = el('button', 'chip', '🔁 שורה ' + ctx.line.num); b.type = 'button'; b.addEventListener('click', () => vaPractise(ctx.line)); acts.append(b); }
    if (x.tool === 'transpose' && ctx.key != null) { const b = el('button', 'chip on', 'להחיל סולם ' + REC.lr(vaSigned(ctx.key))); b.type = 'button'; b.addEventListener('click', () => { if (REC.on) return; setSemi(ctx.key); ui.status('הסולם שונה ל-' + REC.lr(vaSigned(ctx.key)) + ' (אפשר לחזור ב"איפוס" של הסולם)'); vaRender(); }); acts.append(b); }
    if (PR_EX[id]) { const b = el('button', 'chip on', '🏋️ לתרגל עכשיו'); b.type = 'button'; b.addEventListener('click', () => prOpen(PR_EX[id], { cents: ctx.tone })); acts.append(b); } // (v0.8.0) live practice
    if (acts.childNodes.length) box.append(acts);
    return box;
  }
  async function vaAllData() { // every take of every song: its analysis (phone / pack); the ones without one
    const out = [], todo = [], seen = new Set(), songs = (E.index && E.index.songs) || [];
    let recs = []; try { recs = (await REC.op('takes', 'readonly', (st) => st.getAll())) || []; } catch (e) { recs = []; }
    for (const s of songs) {
      const idx = PKS ? (s.id === E.song.id ? PK.idx : await getJson('songs/' + s.id + '/_pack.json')) : null;
      const ids = new Set([...Object.keys((idx && idx.takes) || {}), ...recs.filter((t) => t.songId === s.id).map((t) => t.id)]);
      for (const tid of ids) {
        if (seen.has(tid)) continue; seen.add(tid);
        const a = await vaLoad(s.id, tid, idx);
        if (a && a.v === HVo().VOICE_V) out.push(a); else todo.push({ songId: s.id, tid, playable: s.audio !== false, title: s.title });
      }
    }
    return { list: out, todo };
  }
  async function vaAnalyseOther(songId, tid) { // a take of another song: its melody, lines, stems and chunks from its pack
    const base = 'songs/' + songId + '/', song = await getJson(base + 'song.json'), A = await getJson(base + 'analysis.json'), mj = await getJson(base + 'melody.json');
    if (!song || !A || !mj) return null;
    let rec = null, local = true; try { rec = await REC.op('takes', 'readonly', (st) => st.get(tid)); } catch (e) { rec = null; }
    if (!rec) { local = false; rec = await getJson(base + 'takes/' + tid + '/take.json'); }
    if (!rec || rec.id !== tid) return null;
    const C = Math.round(song.chunkFrames * E.SR / song.sampleRate);
    const get = async (id, k) => { const v = await REC.op('tchunks', 'readonly', (st) => st.get(id + ':' + k)).catch(() => undefined); if (v) return v;
      try { const r = await fetch(base + 'takes/' + tid + '/' + PK.fileOf(id + ':' + k)); return r.ok ? new Int16Array(await r.arrayBuffer()) : undefined; } catch (e) { return undefined; } };
    return vaAnalyse(rec, { id: songId, base, song, A, ref: window.HarmonyPitch.melody(mj) }, { get, C, keep: local });
  }
  function vaOpen(scope) {
    VA.scope = scope || VA.scope || 'take';
    $('vaBox').hidden = false; document.body.classList.add('va-on');
    vaRender();
    if (REC.active && !VA.cur) vaUpdate();
  }
  async function vaRender() {
    const H = HVo(), body = $('vaBody'); if (!H || !body) return;
    ['vaTabTake', 'vaTabAll'].forEach((id) => { const on = (id === 'vaTabTake') === (VA.scope === 'take'); $(id).classList.toggle('on', on); $(id).setAttribute('aria-selected', String(on)); });
    const seq = (VA.renderSeq = (VA.renderSeq || 0) + 1);
    body.replaceChildren(el('p', 'va-wait', 'מכין את הדוח…'));
    const all = await vaAllData(); if (seq !== VA.renderSeq) return;
    const agg = H.aggregate(all.list), parts = [];
    const songName = (id) => { const s = ((E.index && E.index.songs) || []).find((q) => q.id === id); return s ? s.title || id : id; };
    const range = agg.m.range; VA.range = range; if (range && Number.isFinite(range.lo)) store.set('harmony.vrange.v1', { lo: range.lo, hi: range.hi, at: Date.now() }); // (v0.8.0) the practice screen's range
    const keyHere = agg.m.keys.find((k) => k.songId === E.song.id) || null;
    const sec = (title) => { const s = el('section', 'va-sec'); s.append(el('h3', 'va-h', title)); parts.push(s); return s; };
    const capTxt = (c) => H.CONF_HE[c];
    if (VA.scope === 'take') {
      const t = REC.active, cur = VA.cur && VA.cur.t === t ? VA.cur.a : null;
      if (!t) { parts.push(el('p', 'va-wait', 'אין עדיין הקלטה לשיר הזה. מקליטים (⏺), והניתוח יופיע כאן.')); }
      else if (!PV.ref || !HV.A) { parts.push(el('p', 'va-wait', 'לשיר הזה אין מנגינה לניתוח.')); }
      else if (!cur) { parts.push(el('p', 'va-wait', 'מנתח את „\u2068' + t.name + '\u2069”… (בטלפון בלבד)')); vaUpdate(); }
      else {
        const m = cur.m, cap = H.capFor(cur.voicedSec, null), fnd = H.findings(m, { cap, keyHere, curKey: mix.semi || 0 }), probs = fnd.filter((x) => !x.tip);
        const s1 = sec('בקצרה');
        const L = m.lines, mins = (cur.voicedSec / 60).toFixed(1);
        s1.append(el('p', 'va-sum', '„\u2068' + t.name + '\u2069”: ' + mins + ' דקות שירה; ' + L.sung + ' שורות נמדדו — 🟢 ' + L.green + ' · 🟡 ' + L.yellow + ' · 🔴 ' + L.red + (L.grey ? ' · ⚪ ' + L.grey + ' לא הושרו' : '') + '. ' + (m.pIn != null ? m.pIn + '% מהשירה בטון.' : '')));
        s1.append(el('p', 'va-sum', cur.voicedSec < VA_MIN_VOICED_S ? 'בהקלטה הזו כמעט לא נשמעה שירה, אז אין עדיין מה לנתח (אם שרת — כדאי לבדוק את המיקרופון).' : probs.length ? 'הכי בולט: ' + probs[0].title + '.' : 'לא נמצא משהו בולט בהקלטה הזו — יפה!'));
        s1.append(el('p', 'va-conf', capTxt(cap) + (cap < 2 ? ' (הקלטה אחת' + (cur.voicedSec < 30 ? ', וקצרה' : '') + ' — ככל שיהיו יותר הקלטות, הניתוח יהיה בטוח יותר)' : '')));
        vaFindings(sec('3 הדברים הבולטים'), fnd, cur, cur.voicedSec < VA_MIN_VOICED_S);
        const rows = vaRows().filter((x) => x.score && (x.score.col === 'red' || x.score.col === 'yellow')).sort((p, q) => (p.score.col === q.score.col ? p.score.pIn - q.score.pIn : p.score.col === 'red' ? -1 : 1)).slice(0, 6);
        const s3 = sec('שורות לתרגול');
        if (!rows.length) s3.append(el('p', 'va-sum', cur.voicedSec < VA_MIN_VOICED_S || !L.sung ? 'אין עדיין שורות שהושרו בהקלטה הזו.' : 'אין שורות אדומות או צהובות. 🎉'));
        rows.forEach((x) => s3.append(vaLineRow(x, cur.oct)));
        const series = agg.series.filter((q) => q.songId === E.song.id);
        const s4 = sec('התקדמות בשיר הזה (' + series.length + ' הקלטות)'); VA_MET.forEach((met) => s4.append(vaChart(series, met)));
      }
    } else {
      const m = agg.m;
      if (!agg.takes) parts.push(el('p', 'va-wait', 'אין עדיין הקלטות מנותחות.'));
      else {
        const cap = H.capFor(m.voicedSec, agg.takes), fnd = H.findings(m, { cap, keyHere, curKey: mix.semi || 0 }), probs = fnd.filter((x) => !x.tip);
        const s1 = sec('בקצרה');
        s1.append(el('p', 'va-sum', agg.takes + ' הקלטות ב-' + m.songs + ' שירים, ' + (m.voicedSec / 60).toFixed(1) + ' דקות שירה. ' + (m.pIn != null ? m.pIn + '% מהשירה בטון.' : '')));
        s1.append(el('p', 'va-sum', m.voicedSec < VA_MIN_VOICED_S ? 'עדיין אין מספיק שירה מוקלטת כדי לנתח את הקול.' : probs.length ? 'הכי בולט: ' + probs[0].title + '.' : 'לא נמצא משהו בולט — יפה!'));
        s1.append(el('p', 'va-conf', capTxt(cap) + (cap < 2 ? ' (מעט הקלטות או הקלטות קצרות עדיין)' : '') + (!m.timingTrust && m.timing.n ? ' · התזמון נמדד רק בהקלטות רמקול / בלי כיול — פחות מדויק' : '')));
        vaFindings(sec('3 הדברים הבולטים'), fnd, null, m.voicedSec < VA_MIN_VOICED_S);
        const sr = sec('הטווח הנוח שלך');
        sr.append(el('p', 'va-sum', range ? 'צלילים ששרת בטון בביטחון: ' + REC.lr(H.noteName(range.lo) + '–' + H.noteName(range.hi)) + ' (' + range.n + ' צלילים). ' + capTxt(Math.min(cap, range.n >= 8 ? 2 : 1)) + '.' : 'עדיין אין מספיק שירה כדי לקבוע טווח.'));
        m.keys.forEach((k) => {
          const here = k.songId === E.song.id, cur = here ? mix.semi || 0 : 0, gain = k.fitBest - H.fitAt(k, cur);
          const p = el('p', 'va-key', songName(k.songId) + ': ' + (k.best === cur || gain < 100 * H.K.RANGE_FIT_GAIN ? 'הסולם ' + (here ? 'הנוכחי' : 'המקורי') + ' מתאים (' + H.fitAt(k, cur) + '% מהמנגינה בטווח)' : 'מוצע סולם ' + REC.lr(vaSigned(k.best)) + ' — ' + k.fitBest + '% מהמנגינה בטווח (עכשיו ' + H.fitAt(k, cur) + '%)'));
          if (here && k.best !== cur && gain >= 100 * H.K.RANGE_FIT_GAIN) { const b = el('button', 'chip on', 'להחיל'); b.type = 'button'; b.addEventListener('click', () => { if (REC.on) return; setSemi(k.best); vaRender(); }); p.append(' ', b); }
          sr.append(p);
        });
        const s4 = sec('התקדמות לאורך ההקלטות (כל השירים)'); VA_MET.forEach((met) => s4.append(vaChart(agg.series, met)));
      }
      if (all.todo.length) {
        const sx = sec('הקלטות שעוד לא נותחו: ' + all.todo.length), can = all.todo.filter((x) => x.playable);
        if (can.length) { const b = el('button', 'chip on', 'לנתח עכשיו (' + can.length + ')'); b.type = 'button'; b.id = 'vaRunAll';
          b.addEventListener('click', async () => { b.disabled = true; let i = 0; for (const x of can) { b.textContent = 'מנתח ' + (++i) + '/' + can.length + '…'; try { if (x.songId === E.song.id) { const t = REC.takes.find((q) => q.id === x.tid); if (t) await vaAnalyse(t); } else await vaAnalyseOther(x.songId, x.tid); } catch (e) { VA.log.push({ at: Date.now(), error: String(e) }); } } vaRender(); });
          sx.append(b); }
        if (all.todo.length > can.length) sx.append(el('p', 'va-conf', (all.todo.length - can.length) + ' מהן של שירים שהוסרו מהטלפון — ינותחו אחרי ייבוא השיר מחדש.'));
      }
    }
    const sn = sec('לתשומת לב');
    sn.append(el('p', 'va-note', '🔒 הניתוח נעשה בטלפון בלבד. ההקלטות והתוצאות לא נשלחות לשום מקום; התוצאות נשמרות בקובץ השיר שלך.'),
      el('p', 'va-note', 'התזמון, הכניסות וסופי השורות נמדדים ביחס לזמר המקורי של השיר, באותה שיטה בדיוק — כך שסגנון של המקור לא נחשב טעות.'),
      el('p', 'va-note', '👩‍🏫 אפליקציה מודדת גובה, תזמון ועוצמה. מורה לפיתוח קול שומע/ת הרבה יותר (נשימה, תנוחה, צבע הקול, מתח) ויכול/ה להוסיף את מה שאפליקציה לא יכולה.'),
      el('p', 'va-note', 'התרגילים כלליים ואינם ייעוץ רפואי. אם יש כאב, צרידות או עייפות בקול — לעצור ולנוח.'));
    body.replaceChildren(...parts);
  }
  function vaFindings(box, fnd, cur, thin) {
    const top = fnd.slice(0, 3);
    if (!top.length) { box.append(el('p', 'va-sum', thin ? 'אין עדיין מספיק שירה כדי למצוא דברים לשיפור.' : 'אין ממצאים בולטים. אפשר להמשיך לתרגל עם 🔁 על שורות שאוהבים.')); return; }
    const rows = cur ? vaRows().filter((x) => x.score && x.score.col !== 'grey') : [], worst = rows.slice().sort((p, q) => p.score.pIn - q.score.pIn)[0] || null;
    top.forEach((f, i) => {
      const c = el('article', 'va-f' + (f.tip ? ' tip' : ''));
      c.append(el('p', 'va-f-t', (i + 1) + '. ' + f.title), el('p', 'va-f-x', f.text), el('p', 'va-conf', f.confText));
      // the exercise's own targets: the line most affected (by number) and its first note as the 🎵 tone
      let line = worst; if (cur && /Line|phraseEnd|longLines/.test(f.id)) { const ln = (cur.m.ends.breath[0] || cur.m.ends.long[0]); const r = ln && rows.find((x) => x.lines.some((s) => s.n === ln)); if (r) line = r; }
      if (cur && f.id === 'scoop') { const e = (cur.ent || []).find((q) => q.scoop); const r = e && rows.find((x) => x.lines.some((s) => s.n === e.line)); if (r) line = r; }
      if (cur && /High|Mid|Low|sharp|flat/.test(f.id)) { const r = rows.slice().sort((p, q) => Math.abs(q.score.med) - Math.abs(p.score.med))[0]; if (r) line = r; }
      // no line (all takes): the middle of his comfortable range
      const R0 = !cur && VA.range ? Math.round((VA.range.lo + VA.range.hi) / 2) : null;
      const tone = line ? vaFirstNote(line.lines[0], cur ? cur.oct : 0) : R0 != null ? (R0 - 33) * 100 : NaN;
      f.ex.slice(0, 2).forEach((id) => { const x = vaExercise(id, { tone, line, key: f.key }); if (x) c.append(x); });
      box.append(c);
    });
  }
  function vaLineRow(x, oct) {
    const sc = x.score, row = el('div', 'va-line sc-' + sc.col);
    const b = el('button', 'va-line-b'); b.type = 'button'; b.append(el('span', 'va-line-n', vaNumbers(sc, x.num)));
    b.setAttribute('aria-label', vaNumbers(sc, x.num) + '. לחיצה: מעבר לשורה וחזרה עליה');
    b.addEventListener('click', () => vaPractise(x));
    const acts = el('div', 'va-acts');
    const tb = el('button', 'chip', '🎵 צליל פתיחה'); tb.type = 'button'; tb.addEventListener('click', () => vaTone(vaFirstNote(x.lines[0], oct), 1.6));
    const lb = el('button', 'chip', '🔁 חזרה'); lb.type = 'button'; lb.addEventListener('click', () => vaPractise(x));
    acts.append(lb, tb);
    row.append(b, acts);
    return row;
  }
  function vaInit() {
    $('vaOpen').addEventListener('click', () => vaOpen('take'));
    $('vaClose').addEventListener('click', vaHide);
    $('vaTabTake').addEventListener('click', () => { VA.scope = 'take'; vaRender(); });
    $('vaTabAll').addEventListener('click', () => { VA.scope = 'all'; vaRender(); });
  }
  function asSet(on) { AS.on = !!on; store.set('harmony.autoscroll.v1', AS.on); asSync(); if (AS.on) { LY.userScrollAt = 0; asFollow(); } }
  const LY_KEY = () => 'harmony.lyrics.v1.' + E.song.id;
  const LK_KEY = () => 'harmony.lyrics.auto.v1.' + E.song.id; // (v0.14.0) the lookup's answer + the hidden ids
  function lyLoad() {
    const v = store.get(LY_KEY()), own = !!(v && typeof v.text === 'string' && v.text.trim()), pk0 = v && v.noAuto ? null : LY.pack;
    const lk = lyLook(store.get(LK_KEY()) || LY.lookF, (HV.A && HV.A.phrases) || []); // (v0.14.0)
    const src = lyPick(own, pk0, lk), pk = src === 'pack' ? pk0 : src === 'look' ? lk : null; LY.src = src;
    LY.text = own ? v.text : pk ? pk.text : '';
    LY.fix = own && v.fix && typeof v.fix === 'object' ? v.fix : {};
    LY.fine = own && v.fine && typeof v.fine === 'object' ? v.fine : {}; // (v0.7.1) lines fine-tuned with ‎−0.1 / ‎+0.1
    LY.auto = own && v.auto && v.auto.v === 1 && Array.isArray(v.auto.lines) ? v.auto : pk ? pk.auto : null;
    LY.lines = LY.text.split('\n').map((l) => l.trim()).filter(Boolean);
    lyMatch();
  }
  // the user's own state; the automatic lines are stored only once the user changes something (then with their timing)
  const lySave = () => (LY.src = LY.text.trim() ? 'own' : null, store.set(LY_KEY(), { text: LY.text, fix: LY.fix, fine: LY.fine, ...(LY.auto ? { auto: LY.auto } : {}), ...(LY.text.trim() ? {} : { noAuto: 1 }) })); // (v0.14.0) saved = the user's own text (a found-by-name one too)
  // ---- automatic lyrics (lane L): the pack's lyrics.json -> { text, auto }, or null when it is missing / unusable
  const lyNorm = (t) => String(t).replace(/\s+/g, ' ').trim();
  const lyHash = (t) => { let h = 0x811c9dc5; const s = lyNorm(t); for (let k = 0; k < s.length; k++) h = Math.imul(h ^ s.charCodeAt(k), 0x01000193); return (h >>> 0).toString(36); };
  // ASR junk: a hallucinated line (one character repeated 8+ times, or a token longer than 40 chars) is never shown
  const lyJunk = (t) => /(.)\1{7,}/u.test(t.replace(/\s+/g, '')) || t.split(' ').some((w) => w.length > 40);
  function lyPack(j) {
    if (!j || j.v !== 1 || !Array.isArray(j.lines) || j.source === 'none' || (j.verdict !== 'ok' && j.verdict !== 'weak')) return null;
    const out = [];
    for (const l of j.lines) {
      if (!l || typeof l.t !== 'string') return null;
      const t = lyNorm(l.t); if (!t) continue;
      if (lyJunk(t)) continue; // ASR junk
      const ok = l.ok === true && Number.isFinite(l.s), raw = ok && Array.isArray(l.w) ? l.w : [];
      const w = raw.filter((x) => Array.isArray(x) && Number.isFinite(x[1]) && Number.isFinite(x[2]) && x[2] >= x[1]).map((x) => [x[1], x[2]]);
      out.push({ t, h: lyHash(t), s: Number.isFinite(l.s) ? l.s : null, ok, ...(l.tm === 'lrc' ? { tm: 'lrc' } : {}), w: w.length === raw.length && w.length === t.split(' ').length ? w : [] });
    }
    if (!out.length) return null;
    return { text: out.map((x) => x.t).join('\n'), auto: { v: 1, source: String(j.source), verdict: j.verdict, lines: out.map(({ t, ...x }) => x) } };
  }
  // ---- (v0.14.0) lyrics looked up by name: pure helpers (tests/lyrics-lookup) ----
  // which text is shown: 'own' (pasted / edited) > 'pack' (lyrics.json, ok or weak) > 'look' (found by name) > null
  const lyPick = (own, pack, look) => (own ? 'own' : pack ? 'pack' : look ? 'look' : null);
  // one global offset of the LRC stamps onto the phrase starts: scan −30..+30 s by 0.1 s, a stamp matches within 0.5 s of
  // a phrase start; the best offset (most matches, then the smallest |offset|) is refined to the median of its matched
  // differences. ok = at least 4 matches and at least half the stamps (lrc_crosscheck, looser: phrases are energy)
  function lyFit(stamps, phr) {
    const ts = stamps.filter(Number.isFinite), ps = phr.map((p) => p.t0).filter(Number.isFinite).sort((a, b) => a - b);
    if (!ts.length || !ps.length) return { ok: false, n: 0, of: ts.length, offset: 0 };
    const near = (x) => { let lo = 0, hi = ps.length - 1; while (lo < hi) { const m = (lo + hi) >> 1; if (ps[m] < x) lo = m + 1; else hi = m; }
      let d = ps[lo] - x; if (lo > 0 && Math.abs(ps[lo - 1] - x) < Math.abs(d)) d = ps[lo - 1] - x; return d; }; // nearest phrase start − x
    const TOL = 0.5 + 1e-9;
    let best = -1, bo = 0;
    for (let k = -300; k <= 300; k++) {
      const o = k / 10; let n = 0; for (const t of ts) if (Math.abs(near(t + o)) <= TOL) n++;
      if (n > best || (n === best && Math.abs(o) < Math.abs(bo))) { best = n; bo = o; }
    }
    const ds = []; for (const t of ts) { const d = near(t + bo); if (Math.abs(d) <= TOL) ds.push(bo + d); }
    ds.sort((a, b) => a - b);
    const med = ds.length ? (ds.length % 2 ? ds[ds.length >> 1] : (ds[ds.length / 2 - 1] + ds[ds.length / 2]) / 2) : bo;
    const offset = Math.round(med * 1000) / 1000;
    return { ok: best >= 4 && best >= ts.length / 2, n: best, of: ts.length, offset };
  }
  // the stored answer (harmony.lyrics.auto.v1.<id> / lyrics-lookup.json) -> { text, auto } like lyPack, or null (none,
  // hidden, unusable). Synced + a good fit: every stamped line starts at stamp + offset (tm 'lrc': an anchor in lyTime);
  // else the lines are mapped like pasted text. No phrases (no analysis): untimed.
  function lyLook(j, phr) {
    if (!j || j.v !== 1 || j.source !== 'lookup' || !Array.isArray(j.lines) || !j.lines.length) return null;
    const ls = [];
    for (const l of j.lines) { if (!l || typeof l.t !== 'string') return null; const t = lyNorm(l.t); if (t && !lyJunk(t)) ls.push({ t, s: Number.isFinite(l.s) ? l.s : null }); }
    if (!ls.length) return null;
    const fit = j.synced ? lyFit(ls.map((x) => x.s), phr || []) : { ok: false };
    const out = ls.map((x) => ({ h: lyHash(x.t), s: fit.ok && x.s != null ? Math.round((x.s + fit.offset) * 1000) / 1000 : null, ok: false, ...(fit.ok && x.s != null ? { tm: 'lrc' } : {}), w: [] }));
    return { text: ls.map((x) => x.t).join('\n'), auto: { v: 1, source: 'lookup', verdict: 'lookup', providerId: j.providerId, ...(fit.ok ? { offset: fit.offset } : {}), lines: out } };
  }
  // the ids the user hid ("לא תואם? הסתר"), never offered again
  const lkRejected = (j) => (j && Array.isArray(j.rejected) ? j.rejected.filter((x) => Number.isSafeInteger(x) && x >= 0).slice(-64) : []);
  // a new answer (r = the native job's {found, synced, providerId, durDiff, lines}) -> the stored doc; the hidden ids stay
  const lkDoc = (prev, r, at) => ({ v: 1, at, source: 'lookup', verdict: 'unverified', synced: !!r.synced, providerId: r.providerId, durDiff: r.durDiff,
    lines: (r.lines || []).filter((l) => l && typeof l.t === 'string').map((l) => ({ t: l.t, s: Number.isFinite(l.s) ? l.s : null })), rejected: lkRejected(prev) });
  // "לא תואם? הסתר": the lines go, their id joins the hidden ones
  const lkHide = (prev, at) => { const rj = lkRejected(prev), id = prev && prev.providerId; if (Number.isSafeInteger(id) && !rj.includes(id)) rj.push(id); return { v: 1, at, source: 'lookup', lines: [], rejected: rj.slice(-64) }; };
  // ---- (end v0.14.0 pure helpers)
  // ---- (v0.14.0) the button: shown only with the bridge (a newer app), a network, a song title and no lyrics at all
  const LKS = ANDROID && typeof window.Android.lyricsLookup === 'function' && typeof window.Android.lyricsJob === 'function';
  const LK = { busy: false, msg: '' };
  const LK_WAIT_MS = 90000; // no answer by then: given up (no automatic retry)
  const lkOnline = () => { try { if (typeof window.Android.netOnline === 'function') return !!window.Android.netOnline(); } catch (e) { /* old bridge */ } return navigator.onLine !== false; };
  const lkStored = () => store.get(LK_KEY()) || LY.lookF || null;
  function lkSync(look) {
    const b = $('lyrLookup'), h = $('lyrLkHide'), m = $('lyrLkMsg'); if (!b) return;
    const can = LKS && !!E.song && !!String(E.song.title || '').trim() && !LY.lines.length && (LK.busy || lkOnline());
    b.hidden = !can; b.disabled = LK.busy; b.textContent = LK.busy ? 'מחפש מילים…' : '🎤 טעינת מילים'; b.setAttribute('aria-busy', String(LK.busy));
    if (h) h.hidden = !look || LK.busy;
    if (m) { m.hidden = !LK.msg; m.textContent = LK.msg; }
  }
  const lkRefresh = () => { lyLoad(); applyDir(); lyBuild(); if (HV.A) lyView(audibleSec()); };
  // the answer into the song's pack as lyrics-lookup.json (the user's part; never lyrics.json): one append save
  async function lkPack(doc, tries) {
    if (!PKS || !E.song) return;
    const id = E.song.id, A = window.Android;
    if (!((E.index && E.index.songs) || []).some((x) => x.id === id)) return; // no pack yet: the phone's copy only
    if (REC.on || REC.busy) { if ((tries || 0) < 40) setTimeout(() => lkPack(doc, (tries || 0) + 1), 3000); return; } // never while recording
    try {
      const txn = 'k' + Date.now().toString(36) + Math.random().toString(36).slice(2, 7), u8 = utf8(JSON.stringify(doc));
      if (!A.stageBegin(txn) || !A.stageChunk(txn, 'lyrics-lookup.json', b64(u8), false)) return;
      const r = await PK.job(A.packCommit(id, txn, JSON.stringify({ puts: [{ name: 'lyrics-lookup.json', file: 'lyrics-lookup.json' }], dels: [] })));
      PK.log.push({ songId: id, at: Date.now(), puts: 1, staged: u8.length, lookup: 1, state: r.state, code: r.code }); if (PK.log.length > 50) PK.log.shift();
      if (r.state !== 'done' && r.code === 'busy' && (tries || 0) < 40) setTimeout(() => lkPack(doc, (tries || 0) + 1), 3000);
    } catch (e) { PK.err = String(e); }
  }
  function lkSet(doc) { store.set(LK_KEY(), doc); LY.lookF = null; lkPack(doc); }
  async function lkRun() {
    if (LK.busy || !LKS || !E.song) return;
    if (!lkOnline()) { LK.msg = 'אין חיבור לאינטרנט, נסו שוב מאוחר יותר'; lkSync(false); return; }
    const spec = { title: String(E.song.title || ''), artist: String(E.song.artist || ''), dur: E.song.frames / E.song.sampleRate, rejected: lkRejected(lkStored()) };
    let j = ''; try { j = String(window.Android.lyricsLookup(JSON.stringify(spec)) || ''); } catch (e) { j = ''; }
    LK.busy = true; LK.msg = ''; lkSync(false);
    const t0 = Date.now();
    let r = null;
    while (j) {
      await new Promise((res) => setTimeout(res, 300));
      try { r = JSON.parse(window.Android.lyricsJob(j)); } catch (e) { r = null; }
      if (r && r.state !== 'running') break;
      if (Date.now() - t0 > LK_WAIT_MS) { r = { state: 'error', code: 'slow' }; break; }
    }
    LK.busy = false;
    if (!j) r = { state: 'error', code: 'net' };
    if (r && r.state === 'done' && r.found && Array.isArray(r.lines) && r.lines.length) {
      lkSet(lkDoc(lkStored(), r, Date.now())); LK.msg = ''; lkRefresh();
      if (LY.src !== 'look') LK.msg = 'לא נמצאו מילים לשיר הזה'; // (an answer with no usable line)
    } else LK.msg = r && r.state === 'done' ? 'לא נמצאו מילים לשיר הזה'
      : r && r.code === 'offline' ? 'אין חיבור לאינטרנט, נסו שוב מאוחר יותר'
      : r && r.code === 'slow' ? 'החיפוש לקח יותר מדי זמן, נסו שוב מאוחר יותר'
      : 'לא הצלחתי לחפש מילים עכשיו, נסו שוב מאוחר יותר';
    lyMatch();
  }
  function lkWire() {
    if (!$('lyrLookup')) return;
    $('lyrLookup').addEventListener('click', lkRun);
    $('lyrLkHide').addEventListener('click', () => { lkSet(lkHide(lkStored(), Date.now())); LK.msg = ''; lkRefresh(); });
    const re = () => { if (!LK.busy) lyMatch(); };
    window.addEventListener('online', re); window.addEventListener('offline', re);
    document.addEventListener('visibilitychange', () => { if (!document.hidden) re(); });
  }
  // LY.am[i] = the automatic line timing line i still matches (same text, in order, within a short look-ahead) or null
  function lyMatch() {
    const L = LY.lines.length, al = (LY.auto && LY.auto.lines) || []; LY.am = new Array(L).fill(null);
    let j = 0;
    for (let i = 0; i < L && j < al.length; i++) {
      const h = lyHash(LY.lines[i]);
      for (let k = j; k < Math.min(al.length, j + 12); k++) if (al[k] && al[k].h === h) { LY.am[i] = al[k]; j = k + 1; break; }
    }
    const src = $('lyrSrc'); if (!src) return;
    const all = L > 0 && L === al.length && LY.am.every(Boolean); // the lines shown are the automatic ones
    const look = all && LY.auto.source === 'lookup'; // (v0.14.0) found by name: always said so (the hide action only while not edited)
    src.hidden = !all; src.textContent = !all ? '' : look ? 'נמצאו לפי שם השיר · ייתכן שלא תואמות' : 'מילים אוטומטיות' + (LY.auto.verdict === 'weak' ? ' · חלקי' : '');
    try { lkSync(look && LY.src === 'look'); } catch (e) { /* before the lookup UI */ }
  }
  // the line's words lit in turn: an ok line aligned to the vocals (no lrc fill), also under a weak verdict, one time pair
  // per word (else the line is lit as a whole)
  const lyKar = (i) => { const a = LY.am[i]; return !!(a && a.ok && (LY.auto.verdict === 'ok' || LY.auto.verdict === 'weak') && !a.tm && Array.isArray(a.w) && a.w.length && Number.isFinite(a.s) && a.w.length === lyNorm(LY.lines[i]).split(' ').length); };
  // starts for lines with weights w[] onto phrases phr[] ({t0,t1}); first line on the first phrase
  function mapLines(w, phr) {
    const L = w.length, P = phr.length;
    if (!L) return [];
    if (!P) return w.map(() => null);
    const cw = [0]; w.forEach((x) => cw.push(cw[cw.length - 1] + x)); const W = cw[L];
    const cv = [0]; phr.forEach((p) => cv.push(cv[cv.length - 1] + Math.max(0.05, p.t1 - p.t0))); const V = cv[P];
    const C = (i) => cw[i] / W, Vf = (j) => cv[j] / V;
    if (L <= P) {               // choose phrase j_i for each line (j_0 = 0, strictly increasing)
      const INF = 1e9, D = [], B = [];
      for (let i = 0; i < L; i++) { D.push(new Float64Array(P).fill(INF)); B.push(new Int32Array(P)); }
      D[0][0] = 0;
      for (let i = 1; i < L; i++) {
        let best = INF, bj = -1;
        for (let j = i; j <= P - (L - i); j++) {
          if (D[i - 1][j - 1] < best) { best = D[i - 1][j - 1]; bj = j - 1; }
          D[i][j] = best + Math.abs(C(i) - Vf(j)); B[i][j] = bj;
        }
      }
      let j = L - 1; let bestv = INF;
      for (let k = L - 1; k < P; k++) if (D[L - 1][k] < bestv) { bestv = D[L - 1][k]; j = k; }
      const js = new Array(L); for (let i = L - 1; i >= 0; i--) { js[i] = j; j = B[i][j]; }
      return js.map((jj) => phr[jj].t0);
    }
    // L > P: choose the first line k_j of each phrase (k_0 = 0, strictly increasing), then split phrases by length
    const INF = 1e9, D = [], B = [];
    for (let j = 0; j < P; j++) { D.push(new Float64Array(L).fill(INF)); B.push(new Int32Array(L)); }
    D[0][0] = 0;
    for (let j = 1; j < P; j++) {
      let best = INF, bk = -1;
      for (let k = j; k <= L - (P - j); k++) {
        if (D[j - 1][k - 1] < best) { best = D[j - 1][k - 1]; bk = k - 1; }
        D[j][k] = best + Math.abs(C(k) - Vf(j)); B[j][k] = bk;
      }
    }
    const ks = new Array(P); ks[P - 1] = P - 1; let bestv = INF;
    for (let k = P - 1; k < L; k++) if (D[P - 1][k] < bestv) { bestv = D[P - 1][k]; ks[P - 1] = k; }
    for (let j = P - 1; j > 0; j--) ks[j - 1] = B[j][ks[j]];
    const st = new Array(L);
    for (let j = 0; j < P; j++) {
      const a = ks[j], b = j + 1 < P ? ks[j + 1] : L, p = phr[j], tw = cw[b] - cw[a];
      for (let i = a; i < b; i++) st[i] = p.t0 + (p.t1 - p.t0) * (cw[i] - cw[a]) / tw;
    }
    return st;
  }
  function lyTime() {
    const A = HV.A, phr = (A && A.phrases) || [], L = LY.lines.length, dur = E.durF / E.SR;
    const w = LY.lines.map((l) => Math.max(1, l.replace(/\s+/g, '').length));
    // (v0.7.1) a line fine-tuned with ‎−0.1 / ‎+0.1 (LY.fine[i] = what it was before: its "starts now" time, or null =
    // auto) moves alone: the other lines are timed as before it was tuned (no cascade); it takes its own start below
    const fine = LY.fine || {}, isFine = (i) => Object.prototype.hasOwnProperty.call(fine, i) && Number.isFinite(LY.fix[i]);
    const own = (i) => (isFine(i) ? fine[i] : LY.fix[i]);
    // (lane L) an automatic line start (an ok line, or a line placed by the cross-checked line times) is an anchor too,
    // below the user's: it is dropped where it would cross a user pin or the anchor before it
    const aut = (i) => { const a = LY.am[i]; return a && (a.ok || a.tm === 'lrc') && Number.isFinite(a.s) ? a.s : null; };
    const val = (i) => (Number.isFinite(own(i)) ? own(i) : aut(i));
    const pins = Object.keys(LY.fix).map(Number).filter((i) => i >= 0 && i < L && Number.isFinite(own(i))).sort((a, b) => a - b);
    const anchors = [];
    for (let i = 0, p = 0; i < L; i++) {
      while (p < pins.length && pins[p] < i) p++;
      if (pins[p] === i) { anchors.push(i); continue; }
      const v = aut(i); if (v == null) continue;
      const prev = anchors.length ? val(anchors[anchors.length - 1]) : -Infinity, nextPin = p < pins.length ? own(pins[p]) : Infinity;
      if (v > prev + 0.01 && v < nextPin - 0.01) anchors.push(i);
    }
    const st = new Array(L).fill(null);
    let from = 0, t0 = null;
    const seg = (a, b, tA, tB) => { // lines a..b-1 in [tA, tB); line a starts at tA when tA is given
      let ph = phr.filter((p) => p.t1 > (tA == null ? -1 : tA + 0.05) && p.t0 < tB).map((p) => ({ t0: p.t0, t1: p.t1 }));
      if (tA != null) { if (ph.length && ph[0].t0 < tA) ph[0].t0 = tA; if (!ph.length || ph[0].t0 > tA + 0.05) ph.unshift({ t0: tA, t1: Math.min(tA + 2, tB) }); }
      const m = mapLines(w.slice(a, b), ph);
      for (let i = a; i < b; i++) st[i] = m[i - a];
    };
    // (v0.7.2) a pin re-times only the lines AFTER it: the lines before it keep the timing they had without it (each
    // stretch is mapped as if no later pin existed, then cut at the next pin; a line that would start at or after
    // that pin is squeezed just before it)
    anchors.forEach((ai) => {
      if (ai > from) { seg(from, L, t0, dur + 1); const lim = val(ai); for (let k = ai - 1; k >= from; k--) { const cap = lim - 0.01 * (ai - k); if (st[k] == null || st[k] >= cap) st[k] = Math.max(cap, t0 == null ? 0 : t0 + 0.01 * (k - from + 1)); } }
      for (let k = ai; k < L; k++) st[k] = null;
      from = ai; t0 = val(ai);
    });
    seg(from, L, t0, dur + 1);
    Object.keys(LY.fix).map(Number).forEach((i) => { if (i >= 0 && i < L && isFine(i)) st[i] = LY.fix[i]; });
    anchors.forEach((i) => { if (!Number.isFinite(own(i))) st[i] = aut(i); }); // (lane L) exactly, not snapped to a phrase
    for (let i = 1; i < L; i++) if (st[i] == null || st[i - 1] != null && st[i] <= st[i - 1]) st[i] = st[i - 1] == null ? null : st[i - 1] + 0.01;
    LY.starts = st;
  }
  // Rows in time order (v0.2.7): every line spans only its SUNG part — up to the end of the last vocal phrase in its
  // slot (a hand-set start: the phrase containing it; no phrase: at most 4 s) — and any gap of >= 1 bar (downbeats;
  // 2.5 s without them) before the next line becomes an instrumental row "(גשר)" ("(פתיחה)" before the first line,
  // "(סיום)" after the last) whose chords sit in a bar grid: one cell per bar, 4 bars per row, an exact repeat of
  // the previous row shown once with ×n.
  const BARS_PER_ROW = 4;
  function lyRows(starts) {
    const A = HV.A, phr = (A && A.phrases) || [], dur = E.durF / E.SR, st = starts || LY.starts, L = st.length;
    const down = (A && A.downbeats) || [], chords = (A && A.chords) || [];
    const dd = []; for (let k = 1; k < down.length; k++) dd.push(down[k] - down[k - 1]);
    dd.sort((a, b) => a - b);
    const bar = dd.length ? dd[dd.length >> 1] : 0, minGap = bar ? bar * 0.95 : 2.5;
    const next = (i) => { for (let k = i + 1; k < L; k++) if (st[k] != null) return st[k]; return dur; };
    const rows = [];
    const instr = (kind, t0, t1) => {
      // bar cells: boundaries at the downbeats inside [t0, t1); slivers (< 30 % of a bar) join their neighbour
      let b = [t0, ...down.filter((d) => d > t0 + 0.05 && d < t1 - 0.05), t1];
      if (!bar) { b = [t0]; for (let x = t0 + 2.5; x < t1 - 0.5; x += 2.5) b.push(x); b.push(t1); }
      const lim = (bar || 2.5) * 0.3;
      if (b.length > 2 && b[1] - b[0] < lim) b.splice(1, 1);
      if (b.length > 2 && b[b.length - 1] - b[b.length - 2] < lim) b.splice(b.length - 2, 1);
      const cells = [];
      for (let k = 0; k + 1 < b.length; k++) {
        const c0 = b[k], c1 = b[k + 1], cs = [];
        chords.forEach((c) => { if ((c.t0 <= c0 + 0.05 && c.t1 > c0 + 0.05) || (c.t0 > c0 + 0.05 && c.t0 < c1 - 0.05)) cs.push(c); });
        const ded = cs.filter((c, j) => j === 0 || c.label !== cs[j - 1].label);
        cells.push({ t0: c0, t1: c1, ch: ded });
      }
      const key = (cl) => cl.map((c) => c.ch.map((x) => x.label + (x.unsure ? '?' : '')).join(' ')).join('|');
      for (let k = 0; k < cells.length; k += BARS_PER_ROW) {
        const part = cells.slice(k, k + BARS_PER_ROW), prev = rows[rows.length - 1];
        if (prev && prev.kind === kind && prev.cells.length === part.length && prev.t1 >= part[0].t0 - 0.01 && key(prev.cells) === key(part)) {
          prev.rep++; prev.t1 = part[part.length - 1].t1; part.forEach((c, j) => prev.cells[j].more.push([c.t0, c.t1])); continue;
        }
        rows.push({ kind, t0: part[0].t0, t1: part[part.length - 1].t1, rep: 1, cells: part.map((c) => ({ ...c, more: [[c.t0, c.t1]] })) });
      }
    };
    let first = null; for (let k = 0; k < L; k++) if (st[k] != null) { first = st[k]; break; }
    if (first == null) return st.map((_, i) => ({ kind: 'line', i, t0: Infinity, t1: Infinity })); // untimed: plain rows
    if (first >= minGap) instr('intro', 0, first);
    for (let i = 0; i < L; i++) {
      const s0 = st[i]; if (s0 == null) continue;
      const nx = next(i); let e = -1;
      phr.forEach((p) => { if (p.t0 < nx - 0.05 && p.t1 > s0 + 0.5) e = Math.max(e, p.t1); });
      if (e < 0) e = s0 + 4;
      e = Math.min(e, nx);
      const gap = nx - e >= minGap; // < 1 bar: no instrumental row; the chords up to the next line stay on this line
      rows.push({ kind: 'line', i, t0: s0, t1: e, c1: gap ? e : nx });
      if (gap) instr(nx >= dur ? 'outro' : 'bridge', e, nx);
    }
    return rows;
  }
  const BR_LABEL = { intro: '(פתיחה)', bridge: '(גשר)', outro: '(סיום)' };
  function lyRetranspose() { chips.forEach((b) => b.remove()); chips.clear(); HV.ci = -2; HV.ki = -2; if (HV.A) { lyBuild(); harmView(audibleSec(), true); } }
  function lyBuild() {
    lyTime();
    const box = $('lyrLines'), A = HV.A;
    $('lyrEdit').textContent = LY.lines.length ? 'עריכת מילים' : 'הוספת מילים';
    LY.rows = lyRows();
    const els = LY.rows.map((r) => {
      if (r.kind !== 'line') {
        const row = el('div', 'lyr-br ' + r.kind); row.setAttribute('aria-label', BR_LABEL[r.kind]);
        const grid = el('div', 'br-grid'); grid.setAttribute('aria-hidden', 'true');
        r.cells.forEach((c) => {
          const cell = el('span', 'br-cell');
          c.ch.forEach((x) => { const sp = el('span', x.unsure ? 'unsure' : null); sp.append(bdi(trChord(x.label, x.t0))); cell.append(sp); });
          if (!c.ch.length) cell.append(el('span', 'br-none', '·'));
          c.el = cell; grid.append(cell);
        });
        const lab = el('div', 'lyr-words br-label'); const lt = el('bdi', null, BR_LABEL[r.kind]); lt.dir = 'rtl'; lab.append(lt);
        if (r.rep > 1) lab.append(el('span', 'br-rep', ' ×' + r.rep));
        row.append(grid, lab); r.el = row;
        return row;
      }
      const i = r.i, text = LY.lines[i];
      const row = el('div', 'lyr-line' + (LY.fix[i] != null ? ' fixed' : '')); row.dataset.i = i;
      const ch = el('div', 'lyr-ch'); ch.setAttribute('aria-hidden', 'true');
      const t0 = r.t0, t1 = r.c1; // chords of the sung part (+ a gap shorter than a bar)
      r.spans = new Map(); // chord index -> its label (the one sounding is amber while this line is current)
      if (A && t1 > t0) {
        A.chords.forEach((c, ci) => {
          if (!(c.t1 > t0 + 0.05 && c.t0 < t1 - 0.05)) return;
          const sp = el('span', c.unsure ? 'unsure' : null); sp.append(bdi(trChord(c.label, c.t0))); sp.dataset.f = Math.max(0, (c.t0 - t0) / (t1 - t0)); sp.dataset.ci = ci;
          ch.append(sp); r.spans.set(ci, sp);
        });
      }
      const words = el('div', 'lyr-words', lyKar(i) ? null : text); words.dir = 'auto';
      if (lyKar(i)) { // (lane L) one span per word; times follow the line if the user moved its start
        const a = LY.am[i], d = Number.isFinite(r.t0) ? r.t0 - a.s : 0;
        words.classList.add('kar'); r.words = [];
        lyNorm(text).split(' ').forEach((wd, k) => { const sp = el('span', 'lyr-wd', wd); if (k) words.append(' '); words.append(sp); r.words.push({ el: sp, t0: a.w[k][0] + d }); });
      }
      row.append(ch, words); r.el = row;
      return row;
    });
    box.replaceChildren(...els);
    LY.cur = -2; LY.sel = -1; LY.row = null; LY.cell = null; LY.amber = null; LY.wrow = null; LY.wi = -1;
    lyPlaceChords();
    const nL = LY.lines.length || ((A && A.phrases) || []).length; // (v0.7.0) no lyrics: a loop over the song's own lines
    if (LOOP.a != null && (LOOP.a >= nL || LOOP.b >= nL)) { LOOP.a = LOOP.b = null; LOOP.on = false; store.set(LOOP_KEY(), null); } // the lines changed
    loopCalc();
    vaPaint(); // (v0.7.0) the active take's per-line scores on the rows
    pvUpdate();
  }
  // chords sit at their time-proportional spot along the line (RTL: from the right edge), never overlapping: a chord
  // that would collide moves along, and wraps to a second chord row when the line is full (large text)
  function lyPlaceChords() {
    // bar grids: 4 bars across; if any chord name doesn't fit its cell, or a cell needs > 2 lines (large text, narrow screen), every grid shows
    // 2 bars per line instead (the same for all rows, so the bars stay aligned)
    const grids = [...document.querySelectorAll('.br-grid')];
    grids.forEach((g) => g.classList.remove('two'));
    const tight = (c) => c.scrollWidth > c.clientWidth + 1 || c.offsetHeight > 2.5 * (parseFloat(getComputedStyle(c).lineHeight) || 20);
    if (grids.some((g) => [...g.children].some(tight))) grids.forEach((g) => g.classList.add('two'));
    document.querySelectorAll('.lyr-ch').forEach((ch) => {
      const W = ch.clientWidth, spans = [...ch.children]; let x = 0, row = 0, h = 0;
      spans.forEach((sp) => {
        const w = sp.offsetWidth; h = Math.max(h, sp.offsetHeight);
        let want = Math.max(+sp.dataset.f * W, spans[0] === sp ? 0 : x + 8);
        if (want + w > W) { if (x > 0 && want - (want + w - W) < x + 8) { row++; want = 0; } else want = Math.max(0, W - w); }
        sp.style.insetInlineStart = want + 'px'; sp.style.top = (row * h) + 'px'; x = want + w;
      });
      ch.style.height = spans.length ? ((row + 1) * h) + 'px' : '';
    });
  }
  function lyView(t) {
    if (!LY.lines.length || !LY.starts.length) return;
    let i = -1;
    for (let k = 0; k < LY.starts.length; k++) if (LY.starts[k] != null && LY.starts[k] <= t) i = k;
    if (i !== LY.cur) { LY.cur = i; if (HV.trace) HV.trace.push(['ly', performance.now(), t, i]); }
    // the highlighted row: the last row (line or instrumental) that has started; in an instrumental row, its bar
    let r = null; for (const x of LY.rows || []) { if (x.t0 <= t + 1e-6) r = x; else break; }
    if (r !== LY.row) {
      if (LY.row && LY.row.el) LY.row.el.classList.remove('cur');
      LY.row = r;
      if (r && r.el) {
        r.el.classList.add('cur');
        if (AS.on && E.playing && Date.now() - LY.userScrollAt > 4000) asFollow();
      }
    }
    if (PV.res) pvHead(t);
    // sung line: the label of the chord sounding now (the strip's own index HV.ci, same audio clock) is amber
    const amb = r && r.spans ? r.spans.get(HV.ci) || null : null;
    if (amb !== LY.amber) { if (LY.amber) LY.amber.classList.remove('now'); LY.amber = amb; if (amb) amb.classList.add('now'); }
    let cell = null;
    if (r && r.cells) for (const c of r.cells) if (c.more.some(([a, b]) => t >= a && t < b)) { cell = c; break; }
    if (cell !== LY.cell) {
      if (LY.cell && LY.cell.el) LY.cell.el.classList.remove('now');
      LY.cell = cell; if (cell && cell.el) cell.el.classList.add('now');
    }
    // (lane L) the word being sung: sung words stay lit, the current one is amber
    const wr = r && r.words ? r : null; let wi = -1;
    if (wr) for (let k = 0; k < wr.words.length; k++) { if (wr.words[k].t0 <= t + 1e-6) wi = k; else break; }
    if (wr !== LY.wrow || wi !== LY.wi) {
      if (LY.wrow && LY.wrow !== wr) LY.wrow.words.forEach((x) => x.el.classList.remove('past', 'now'));
      if (wr) wr.words.forEach((x, k) => { x.el.classList.toggle('past', k < wi); x.el.classList.toggle('now', k === wi); });
      LY.wrow = wr; LY.wi = wi;
    }
  }
  // ---- direction of the lyric rows (v0.3.0; the chord strip stays the same for every song, v0.3.1): from the pasted
  // lyrics' letters (more Latin / other LTR letters than Hebrew / Arabic -> LTR); no lyrics: song.json "dir" or "lang";
  // else RTL. The app's own UI (header, mixer, buttons) stays Hebrew RTL.
  function musicDir() {
    const t = LY.text || '';
    const rtl = (t.match(/[\u0590-\u05FF\u0600-\u06FF\u0700-\u074F]/g) || []).length;
    const all = (t.match(/\p{L}/gu) || []).length;
    if (all) return rtl * 2 >= all ? 'rtl' : 'ltr';
    const s = E.song || {}, lang = String(s.lang || '').toLowerCase();
    if (s.dir === 'ltr' || s.dir === 'rtl') return s.dir;
    if (lang) return /^(he|iw|ar|fa|ur|yi)\b/.test(lang) ? 'rtl' : 'ltr';
    return 'rtl';
  }
  function applyDir() {
    const d = musicDir(); if (d === HV.dir) return;
    HV.dir = d;
    $('lyrLines').dir = d;
    if (LY.rows) lyPlaceChords();
  }
  // ---- skip ⏮ ⏭ (v0.3.0): row starts — the lyric rows (lines + instrumental rows); without lyrics the same rows built
  // on one virtual line per vocal phrase. ⏭ = next row start (none: the end); ⏮ = the current row's start if more than
  // 2 s into it, else the previous row's start (none: 0). Plain seek(): same path as the seek bar, any tempo.
  function skipStarts() {
    const A = HV.A; if (!A) return [];
    const rows = LY.lines.length && LY.rows ? LY.rows : lyRows(((A.phrases) || []).map((p) => p.t0));
    const t = [...new Set(rows.map((r) => r.t0).filter((x) => Number.isFinite(x)))].sort((a, b) => a - b);
    return t;
  }
  function skip(dir) {
    if (!E.song || !HV.A) return;
    const T = skipStarts(), now = E.playing ? audibleSec() : posF() / E.SR, dur = E.durF / E.SR;
    if (dir > 0) { const n = T.find((x) => x > now + 0.05); seek(n != null ? n : dur); return; }
    let cur = -1; T.forEach((x, k) => { if (x <= now + 0.05) cur = k; });
    if (cur >= 0 && now - T[cur] > 2) { seek(T[cur]); return; }
    seek(cur >= 1 ? T[cur - 1] : 0);
  }
  // ---- the tapped line's action bar (v0.7.1: ▶️ לכאן, ‎−0.1 / ‎+0.1 and the line's start time; wraps at 360 px)
  const fmtStart = (t) => { const d = Math.round(Math.max(0, t) * 10); return '\u2066' + Math.floor(d / 600) + ':' + String(((d % 600) / 10).toFixed(1)).padStart(4, '0') + '\u2069'; };
  function lyAct(i, row) {
    const bar = el('div', 'lyr-act');
    const rr = LY.rows.find((x) => x.kind === 'line' && x.i === i), timed = !!rr && Number.isFinite(rr.t0);
    if (rr && rr.score) { const sp = el('p', 'lyr-score sc-' + rr.score.col, '🎯 ' + vaNumbers(rr.score, i + 1)); bar.append(sp); } // (v0.7.0) the line's numbers
    if (timed) {
      const go = el('button', 'chip', '▶️ לכאן'); go.type = 'button'; go.dataset.act = 'go'; go.setAttribute('aria-label', 'ניגון משורה ' + (i + 1) + ' (שנייה לפניה)');
      const ea = el('button', 'chip lyr-fine', '\u200e\u22120.1'); ea.type = 'button'; ea.dataset.act = 'earlier'; ea.setAttribute('aria-label', 'להקדים את תחילת השורה בעשירית שנייה');
      const la = el('button', 'chip lyr-fine', '\u200e+0.1'); la.type = 'button'; la.dataset.act = 'later'; la.setAttribute('aria-label', 'לאחר את תחילת השורה בעשירית שנייה');
      const tm = el('span', 'lyr-start', 'מתחילה ב-'); tm.append(fmtStart(rr.t0)); if (LY.fix[i] == null) tm.append(' (אוטומטי)');
      bar.append(go, ea, la, tm);
    }
    const now = el('button', 'chip', 'השורה מתחילה עכשיו'); now.type = 'button'; now.dataset.act = 'now'; bar.append(now);
    if (LY.fix[i] != null) { const au = el('button', 'chip', 'תזמון אוטומטי'); au.type = 'button'; au.dataset.act = 'auto'; bar.append(au); }
    if (timed) {
      const la = el('button', 'chip', '🔁 מכאן'); la.type = 'button'; la.dataset.act = 'loopA'; la.setAttribute('aria-label', 'חזרה: מתחילה בשורה ' + (i + 1));
      const lb = el('button', 'chip', '🔁 עד כאן'); lb.type = 'button'; lb.dataset.act = 'loopB'; lb.setAttribute('aria-label', 'חזרה: עד שורה ' + (i + 1));
      bar.append(la, lb);
    }
    row.append(bar);
    return bar;
  }
  // ▶️ לכאן (v0.7.1): from 1 s before the line's start (auto or pinned; never before 0) and play. A line outside the
  // loop that is on: the loop goes off (with a note) rather than snapping back into it.
  const PRE_ROLL = 1;
  function lyJump(i) {
    const rr = (LY.rows || []).find((x) => x.kind === 'line' && x.i === i); if (!rr || !Number.isFinite(rr.t0) || !E.song) return;
    if (LOOP.on && LOOP.a != null && (i < LOOP.a || i > LOOP.b)) { const nm = loopName(); loopSet(undefined, undefined, false); ui.status('החזרה על ' + nm + ' כובתה: שורה ' + (i + 1) + ' מחוץ לה'); }
    seek(Math.max(0, rr.t0 - PRE_ROLL));
    if (!E.playing) play();
  }
  // ‎−0.1 / ‎+0.1 (v0.7.1): this line's start only (stored in LY.fix, so "תזמון אוטומטי" reverts it), never past its
  // neighbours; then replays from 1 s before the new start
  function lyFine(i, d) {
    const st = LY.starts, cur = st[i]; if (!Number.isFinite(cur)) return;
    if (!Object.prototype.hasOwnProperty.call(LY.fine, i)) LY.fine[i] = Number.isFinite(LY.fix[i]) ? LY.fix[i] : null;
    let lo = 0, hi = E.durF / E.SR;
    for (let k = i - 1; k >= 0; k--) if (Number.isFinite(st[k])) { lo = st[k] + 0.05; break; }
    for (let k = i + 1; k < st.length; k++) if (Number.isFinite(st[k])) { hi = st[k] - 0.05; break; }
    const v = Math.round(clamp(cur + d, lo, Math.max(lo, hi)) * 1000) / 1000;
    if (Math.abs(v - cur) < 0.0005) ui.status('השורה לא יכולה לעבור את השורה ' + (d < 0 ? 'הקודמת' : 'הבאה'));
    LY.fix[i] = v; lySave(); lyBuild();
    const row = document.querySelector('#lyrLines .lyr-line[data-i="' + i + '"]'); if (row) lyAct(i, row);
    lyJump(i);
  }
  function lyInit() {
    ['miniScroll', 'lyrScroll'].forEach((id) => { const b = $(id); if (b) b.addEventListener('click', () => asSet(!AS.on)); });
    if ($('pvToggle')) $('pvToggle').addEventListener('click', () => pvSet(!PV.on));
    if ('ResizeObserver' in window) { let rw = 0; new ResizeObserver(() => { const w = $('lyrLines').clientWidth; if (w !== rw) { rw = w; if (PV.res) pvDraw(); } }).observe($('lyrLines')); }
    asSync();
    const A = HV.A;
    // (v0.14.0) no analysis: the panel only for lyrics found by name (shown untimed) or the button
    if ((!A || !Array.isArray(A.phrases) || !A.phrases.length) && !LKS && !lyLook(lkStored(), [])) return;
    $('lyr').hidden = false;
    lkWire();
    lyLoad(); applyDir();
    const ed = $('lyrEditor'), ta = $('lyrText');
    let delArmed = 0;
    const close = () => { ed.hidden = true; $('lyrDelete').textContent = 'מחיקת המילים'; delArmed = 0; };
    $('lyrEdit').addEventListener('click', () => { if (!ed.hidden) { close(); return; } ta.value = LY.text; ed.hidden = false; $('lyrDelete').hidden = !LY.text; ta.focus(); });
    $('lyrCancel').addEventListener('click', close);
    $('lyrSave').addEventListener('click', () => {
      const text = ta.value.replace(/\r\n?/g, '\n');
      const n = text.split('\n').map((l) => l.trim()).filter(Boolean).length;
      if (n !== LY.lines.length) { LY.fix = {}; LY.fine = {}; } // the lines changed: hand-set starts no longer belong to the same lines
      LY.text = text; LY.lines = text.split('\n').map((l) => l.trim()).filter(Boolean); lyMatch();
      lySave(); close(); applyDir(); lyBuild(); lyView(audibleSec());
    });
    $('lyrDelete').addEventListener('click', () => {
      if (!delArmed) { delArmed = 1; $('lyrDelete').textContent = 'למחוק? לחיצה נוספת'; setTimeout(() => { if (delArmed) close(); }, 4000); return; }
      const lk = lkStored(); if (lk && Array.isArray(lk.lines) && lk.lines.length) lkSet({ v: 1, at: Date.now(), source: 'lookup', lines: [], rejected: lkRejected(lk) }); // (v0.14.0) found-by-name lines go too (not hidden: may be found again)
      LY.text = ''; LY.fix = {}; LY.fine = {}; LY.lines = []; LY.auto = null; LY.src = null; lyMatch(); store.set(LY_KEY(), LY.pack ? { text: '', noAuto: 1 } : null); close(); applyDir(); lyBuild();
    });
    // tap a line -> its actions; "starts now" pins it to the current playback time
    $('lyrLines').addEventListener('click', (e) => {
      const b = e.target.closest('button');
      const row = e.target.closest('.lyr-line'); if (!row) return;
      const i = +row.dataset.i;
      if (b && b.dataset.act === 'now') { LY.fix[i] = Math.round(audibleSec() * 1000) / 1000; delete LY.fine[i]; lySave(); lyBuild(); lyView(audibleSec()); return; }
      if (b && b.dataset.act === 'auto') { delete LY.fix[i]; delete LY.fine[i]; lySave(); lyBuild(); lyView(audibleSec()); return; }
      if (b && b.dataset.act === 'go') { lyJump(i); return; } // (v0.7.1) ▶️ לכאן
      if (b && (b.dataset.act === 'earlier' || b.dataset.act === 'later')) { lyFine(i, b.dataset.act === 'later' ? 0.1 : -0.1); return; } // (v0.7.1) ‎−0.1 / ‎+0.1
      if (b && (b.dataset.act === 'loopA' || b.dataset.act === 'loopB')) { // (v0.5.3) the loop's first / last line
        let a = LOOP.a, z = LOOP.b; if (b.dataset.act === 'loopA') { a = i; if (z == null || z < i) z = i; } else { z = i; if (a == null || a > i) a = i; }
        document.querySelectorAll('.lyr-act').forEach((x) => x.remove()); loopSet(a, z, true); ui.status('חזרה על ' + loopName()); return;
      }
      if (b) return;
      if (Date.now() - (LOOP.lpAt || 0) < 900) return; // (the click that ends a long press)
      const old = row.querySelector('.lyr-act');
      document.querySelectorAll('.lyr-act').forEach((x) => x.remove());
      if (old) return;
      lyAct(i, row);
    });
    // (v0.5.3) long press on a line (600 ms, finger still): repeat that one line
    { let lp = null; const cancel = () => { if (lp) { clearTimeout(lp.t); lp = null; } };
      $('lyrLines').addEventListener('pointerdown', (e) => { const row = e.target.closest('.lyr-line'); if (!row || e.target.closest('button') || e.button > 0) return; cancel();
        lp = { x: e.clientX, y: e.clientY, t: setTimeout(() => { const i = +row.dataset.i; lp = null; if (!Number.isFinite((LY.rows.find((x) => x.kind === 'line' && x.i === i) || {}).t0)) return; LOOP.lpAt = Date.now(); document.querySelectorAll('.lyr-act').forEach((x) => x.remove()); loopSet(i, i, true); ui.status('חזרה על ' + loopName()); try { navigator.vibrate && navigator.vibrate(30); } catch (x) { /* noop */ } }, 600) }; });
      $('lyrLines').addEventListener('pointermove', (e) => { if (lp && Math.hypot(e.clientX - lp.x, e.clientY - lp.y) > 10) cancel(); });
      ['pointerup', 'pointercancel', 'pointerleave'].forEach((ev) => $('lyrLines').addEventListener(ev, cancel));
      $('lyrLines').addEventListener('contextmenu', (e) => { if (e.target.closest('.lyr-line')) e.preventDefault(); }); }
    ['lyrLoop', 'miniLoop'].forEach((id) => $(id).addEventListener('click', () => loopSet(undefined, undefined, !LOOP.on)));
    $('loopCount').addEventListener('click', () => { LOOP.count = !LOOP.count; store.set('harmony.loopcount.v1', LOOP.count); loopUI(); });
    $('loopClear').addEventListener('click', () => loopSet(null, null, false));
    loopLoad();
    ['touchstart', 'wheel', 'keydown'].forEach((ev) => window.addEventListener(ev, () => { LY.userScrollAt = Date.now(); }, { passive: true }));
    window.addEventListener('resize', lyPlaceChords);
    lyBuild();
  }

  // ---------------------------------------------------------------- record-along (v0.4.0)
  // ⏺ records the user (voice / instrument) in sync with the song into a new take; the active take plays as one more
  // channel "ההקלטה שלי" (volume / mute / solo like any stem; mute the original vocals to keep only yours).
  // - Capture: AudioWorklet (rec-worklet.js) on the mic, in the song's own AudioContext: every sample comes with its
  //   context frame c; song frame = c − T0F − L, where L is the round-trip latency (output -> ear/mic -> input)
  //   measured by "כיול" per output route (speaker / wired / bt) — clicks out, mic in, cross-correlation.
  // - Count-in: one bar of clicks at the song's BPM, then playback from the current spot. Only at tempo 100 % (a take
  //   recorded slower would play back slower than it was sung); takes PLAY at any tempo — they are scheduled exactly
  //   like the stems (same anchor, same playbackRate, through the same pitch shifter).
  // - Storage: IndexedDB "harmony": takes (meta) + tchunks ("<take>:<k>" = Int16 mono, song chunk grid, 8 s each).
  //   Takes are only ever added; deleting is explicit (two taps). Playback decodes only the chunk window (like stems).
  // - Headphones mode: echoCancellation / noiseSuppression / autoGainControl off (clean sound); speaker mode: on (the
  //   phone's echo canceller removes the song from the mic, at some cost to quality).
  // v0.4.1 (first device test: USB-C headphones, weak / broken takes): a wired / USB route is always headphones mode
  //   (an unknown route asks once), the mode is shown on the row and speaker takes carry a badge; a live input meter,
  //   a 2 s level check on a fresh mic, per-take peak / RMS -> a stored playback gain (the take itself stays raw) and
  //   an optional gentle AGC; clap-along calibration for headphones; dropout counters (frame gaps, abrupt silences,
  //   write retries) per take; "פרטים" (everything about a take) and "שלח לי" (WAV + JSON to the share sheet).
  // v0.4.2 (second device test: still weak / choppy with AEC off): on Android the default engine is NATIVE capture
  //   (AudioRecord on its own thread into a file, see NativeRec.kt and "native capture" below); the WebView path stays
  //   as the fallback (switch in a take's "פרטים"). Speaker mode always uses the WebView path (its echo canceller).
  // v0.4.3 (device data: 61–112 stamp slips per take were REAL lost quanta on the A56 — takes drifted and broke up;
  //   clipping at 0 dB; WhatsApp showed the shared file but never sent it): native capture is the default in headphones
  //   mode (VOICE_RECOGNITION as in vc16, UNPROCESSED only by opt-in; MODE_NORMAL, session effects off, drops -> silence);
  //   count-in only when believable; clip counter + "too loud" warning; take numbers across all songs; "שלח לי" = one
  //   .zip with read grants that outlive the receiver's screen.
  // v0.4.5: the unsent v0.4.3 scope; fine-tune = ±1 ms buttons only (no slider; held: 5 then 10 ms steps; ±500 ms;
  //   איפוס); native capture keeps vc16's VOICE_RECOGNITION, UNPROCESSED only by the "מקור: ללא עיבוד" switch in פרטים.
  const MINE = { id: 'mine', label: 'ההקלטה שלי', take: true };
  const REC = {
    on: false, busy: false, takes: [], active: null, mod: null, cur: null, mode: null,
    idb() {
      if (REC.dbp) return REC.dbp;
      REC.dbp = new Promise((res, rej) => {
        const q = indexedDB.open('harmony', 1);
        q.onupgradeneeded = () => { const db = q.result; db.createObjectStore('takes', { keyPath: 'id' }); db.createObjectStore('tchunks'); };
        q.onsuccess = () => res(q.result); q.onerror = () => rej(q.error);
      });
      return REC.dbp;
    },
    async op(store, mode, fn, quiet) {
      const db = await REC.idb();
      return new Promise((res, rej) => {
        const t = db.transaction(store, mode), st0 = t.objectStore(store); let out; const put = [];
        // (v0.6.0) a take record written -> its take.json goes to the song's pack (quiet: a record that came FROM the pack)
        const st = !quiet && store === 'takes' && mode === 'readwrite' ? { put: (v, k) => { put.push(v); return st0.put(v, k); }, delete: (k) => st0.delete(k), get: (k) => st0.get(k), getAll: (q) => st0.getAll(q) } : st0;
        const r = fn(st); if (r) r.onsuccess = () => { out = r.result; };
        t.oncomplete = () => { put.forEach((v) => { if (v && v.id && v.songId) PK.mark(v.songId, { take: v.id, json: true }); }); res(out); };
        t.onerror = t.onabort = () => rej(t.error);
      });
    },
    // (v0.6.0) a chunk the phone no longer keeps (it is in the song's pack) is read from the pack
    getChunk: (id, k) => REC.op('tchunks', 'readonly', (st) => st.get(id + ':' + k)).then((v) => (v !== undefined || !PKS ? v : PK.chunk(id, k))),
    putChunk: (id, k, d) => REC.op('tchunks', 'readwrite', (st) => st.put(d, id + ':' + k)).then((x) => { if (E.song) PK.mark(E.song.id, { take: id.split(':')[0], key: id + ':' + k }); return x; }),
    primaryKey: () => 'harmony.take.v1.' + E.song.id,
    async init() {
      try {
        const all = (await REC.op('takes', 'readonly', (st) => st.getAll())) || [];
        REC.takes = all.filter((t) => t.songId === E.song.id).sort((a, b) => a.created - b.created);
      } catch (e) { REC.takes = []; REC.noDb = true; }
      const p = store.get(REC.primaryKey());
      REC.active = REC.takes.find((t) => t.id === p) || REC.takes[REC.takes.length - 1] || null;
      if (REC.active) E.song.stems.push(MINE);
    },
    // decoded window buffer for song chunk k of the active take (null = nothing recorded there): buffer frame i is song
    // frame sF − D + i, the same layout as a decoded Opus chunk, so schedule() treats it like any stem
    async chunkBuf(k) {
      const t = REC.active; if (!t || t.sr !== E.SR) return null;
      const C = E.Lf, sF = Math.max(0, k * C - E.Mf), eF = Math.min((k + 1) * C + E.Mf, E.durF);
      const nud = Math.round((t.nudgeMs || 0) * E.SR / 1000), a = sF - E.D - nud, b = eF - nud;
      if (b <= t.startF || a >= t.endF) return null;
      const out = new Float32Array(b - a), g = (t.norm === false ? 1 : t.gain || 1) / 32768; // the stored take is raw: its gain applies here
      const src = t.clean && !t.clean.error && t.cleanOn !== false ? t.id + ':c' : t.id; // (v0.5.0) 🧹 on: the cleaned track
      for (let kk = Math.max(0, Math.floor(a / C)); kk * C < b; kk++) {
        const d = await REC.getChunk(src, kk); if (!d) continue;
        const base = kk * C, from = Math.max(a, base), to = Math.min(b, base + C);
        for (let f = from; f < to; f++) out[f - a] = d[f - base] * g;
      }
      const buf = E.ctx.createBuffer(1, out.length, E.SR); buf.copyToChannel(out, 0);
      return buf;
    },
    // output route from Android: "wired" | "bt" | "speaker" | "unknown" (an external output of a type we don't know,
    // e.g. some USB-C adapters); null = no bridge (a browser). v0.4.1: an unknown route asks once "האוזניות מחוברות?"
    route() { try { if (ANDROID && window.Android.audioRoute) return window.Android.audioRoute(); } catch (e) { /* old bridge */ } return null; },
    routeKey() { const r = REC.route(); return r && r !== 'unknown' ? r : (REC.mode === 'speaker' ? 'speaker' : 'wired'); },
    modeKey: () => 'harmony.recmode.v1.' + (REC.route() || 'any'),
    // headphones mode = echo canceller / noise suppression OFF, always (v0.4.1: a wired route can never fall into the
    // speaker mode by itself); mode null = not known yet (asked at the first record / calibration)
    modeInit() {
      const r = REC.route(), saved = store.get(REC.modeKey());
      REC.mode = saved === 'speaker' || saved === 'headphones' ? saved : r === 'wired' || r === 'bt' ? 'headphones' : r === 'speaker' ? 'speaker' : null;
    },
    ask() { // "האוזניות מחוברות?" once per unknown route; resolves 'headphones' | 'speaker'
      REC.asking = true; ui.recState();
      return new Promise((res) => {
        const box = $('recAsk'); REC.askPr = !$('prBox').hidden; REC.askPlace(); box.hidden = false;
        const done = (m) => { box.hidden = true; REC.asking = false; REC.askPr = false; REC.askPlace(); $('recAskYes').onclick = $('recAskNo').onclick = null; REC.mode = m; store.set(REC.modeKey(), m); ui.recState(); res(m); };
        $('recAskYes').onclick = () => done('headphones'); $('recAskNo').onclick = () => done('speaker');
      });
    },
    // (v0.10.1) the question lives in the transport; asked by the practice screen (an overlay over it, and with no
    // song the transport is hidden) it shows in that screen while it is open (an answer there starts the practice only)
    askPlace() { const box = $('recAsk'); if (REC.askPr && !$('prBox').hidden) $('prGo').closest('.pr-go').after(box); else $('recWarn').before(box); },
    async ensureMode() { REC.modeInit(); if (!REC.mode) await REC.ask(); return REC.mode; },
    agc: () => !!store.get('harmony.agc.v1'), // gentle AGC (headphones mode only; speaker mode has the platform's own)
    constraints(noDevice) {
      const hp = REC.mode !== 'speaker';
      const a = { echoCancellation: !hp, noiseSuppression: !hp, autoGainControl: hp ? REC.agc() : true, channelCount: 1 };
      const id = noDevice ? null : REC.micId();
      if (id) a.deviceId = { exact: id };
      return { audio: a };
    },
    // mic choice (wired headphones path): a wired headset's own mic is usually poor, so the phone's built-in mic is
    // preferred when both are listed. Steering = getUserMedia deviceId only (Chromium's own capture inside the WebView
    // can't be redirected natively); Android's AudioManager is used to DETECT whether the headset has a mic at all.
    // Chrome on Android names its inputs e.g. "Speakerphone" / "Headset earpiece" (= the phone's mics), "Wired
    // headset", "USB headset", "Bluetooth headset"; desktop labels vary (classified by keywords, else unknown).
    classify(label) {
      const l = String(label || '');
      if (/bluetooth|hands-?free|\bsco\b|\bbt\b/i.test(l)) return 'bt';
      if (/speakerphone|earpiece|built-?in|internal|bottom|back mic|phone mic|microphone array/i.test(l)) return 'phone';
      if (/wired|headset|headphone|usb|external|line in|jack/i.test(l)) return 'headset';
      return null;
    },
    async scanDevs() {
      let list = [];
      try { list = (await navigator.mediaDevices.enumerateDevices()).filter((d) => d.kind === 'audioinput' && d.deviceId && d.deviceId !== 'default' && d.deviceId !== 'communications'); } catch (e) { /* none */ }
      const devs = { phone: null, headset: null, bt: null, labels: list.map((d) => d.label) };
      // phone mic: Chrome's "Speakerphone" input first — with a wired headset plugged in, Android routes the other
      // phone entries ("Headset earpiece") to the headset's mic anyway
      const rank = (d) => (/speakerphone|built-?in|internal|bottom|back mic/i.test(d.label) ? 0 : 1);
      list.slice().sort((x, y) => rank(x) - rank(y)).forEach((d) => { const c = REC.classify(d.label); if (c && !devs[c]) devs[c] = d.deviceId; });
      let native = null; try { if (ANDROID && window.Android.audioInputs) native = window.Android.audioInputs(); } catch (e) { /* old bridge */ }
      devs.native = native;
      // the choice exists only if both are really there (native says the wired headset has a mic, when we can ask)
      devs.choice = !!(devs.phone && devs.headset && (native == null || /wired|usb/.test(native)));
      const before = REC.devs && REC.devs.choice;
      REC.devs = devs;
      if (before !== devs.choice) ui.recState();
      return devs;
    },
    micPref: () => store.get('harmony.micpref.v1') || 'phone',
    micId() { const d = REC.devs; if (!d || !d.choice) return null; return REC.micPref() === 'headset' ? d.headset : d.phone; },
    latKey: () => (REC.engine() === 'native' ? 'harmony.lat.v1.native.' + REC.routeKey() + (REC.natChoice() ? ':' + REC.micPref() : '')
      : 'harmony.lat.v1.' + REC.routeKey() + (REC.devs && REC.devs.choice ? ':' + REC.micPref() : '')),
    latencyF() {
      const c = store.get(REC.latKey());
      if (c && Number.isFinite(c.ms)) return Math.round(c.ms * E.SR / 1000);
      return Math.round(((E.ctx.outputLatency || E.ctx.baseLatency || 0) + 0.02) * E.SR); // uncalibrated estimate
    },
    async ensureModule() {
      if (REC.mod && REC.mod.ctx === E.ctx) return REC.mod.p;
      REC.mod = { ctx: E.ctx, p: E.ctx.audioWorklet.addModule('rec-worklet.js') };
      return REC.mod.p;
    },
    // stream + recorder node on the song's context. The input path's buffering offset differs a little on every
    // open (measured up to ~9 ms in the test rig), so the mic stays open 60 s after a calibration / take: a calibration
    // and the takes right after it share one stream, hence one offset. Closed at once when the page hides, on the
    // memory release, or when the mode changes.
    async mic() {
      const live = REC.live;
      if (live && live.ctx === E.ctx && live.mode === REC.mode && live.agc === REC.agc() && live.stream.getTracks().every((x) => x.readyState === 'live')) {
        clearTimeout(live.timer); clearTimeout(E.suspendTimer); await E.ctx.resume();
        return live;
      }
      REC.closeMic(); REC.micFallback = false;
      let stream;
      try { stream = await navigator.mediaDevices.getUserMedia(REC.constraints()); } catch (e) {
        if (!REC.micId() || !/Overconstrained|NotFound|NotReadable/.test(e && e.name)) throw e;
        stream = await navigator.mediaDevices.getUserMedia(REC.constraints(true)); REC.micFallback = true; // that mic is gone: default
      }
      let tr = stream.getAudioTracks()[0], set = tr && tr.getSettings ? tr.getSettings() : {};
      await REC.scanDevs(); // labels are readable once permission exists: the choice may appear only now
      const want = REC.micId();
      if (want && !REC.micFallback && set.deviceId && set.deviceId !== want) { // the first open took the default (e.g. the headset's mic)
        try {
          const s2 = await navigator.mediaDevices.getUserMedia(REC.constraints());
          stream.getTracks().forEach((x) => x.stop()); stream = s2;
          tr = stream.getAudioTracks()[0]; set = tr && tr.getSettings ? tr.getSettings() : {};
        } catch (e) { REC.micFallback = true; } // keep the working default stream
      }
      REC.micInfo = { label: tr ? tr.label : '', deviceId: set.deviceId || '', ec: set.echoCancellation, ns: set.noiseSuppression, agc: set.autoGainControl, settings: { ...set } };
      clearTimeout(E.suspendTimer);
      await E.ctx.resume(); await REC.ensureModule();
      const ctx = E.ctx, src = ctx.createMediaStreamSource(stream);
      const node = new AudioWorkletNode(ctx, 'harmony-rec', { numberOfInputs: 1, numberOfOutputs: 1, outputChannelCount: [1] });
      const sink = ctx.createGain(); sink.gain.value = 0;
      src.connect(node); node.connect(sink); sink.connect(ctx.destination);
      const m = { ctx, mode: REC.mode, agc: REC.agc(), stream, node, timer: 0, checked: false };
      m.drop = () => { try { src.disconnect(); node.disconnect(); sink.disconnect(); } catch (e) { /* gone */ } stream.getTracks().forEach((x) => x.stop()); };
      m.close = () => { node.port.onmessage = null; clearTimeout(m.timer); m.timer = setTimeout(() => { if (REC.live === m && !REC.on && !REC.busy) REC.closeMic(); }, 60000); };
      REC.live = m;
      return m;
    },
    closeMic() { const m = REC.live; REC.live = null; if (m) { clearTimeout(m.timer); m.drop(); } },
    clickBuf(freq, ms, amp) {
      const n = Math.round(E.SR * ms / 1000), b = E.ctx.createBuffer(1, n, E.SR), x = b.getChannelData(0);
      for (let i = 0; i < n; i++) x[i] = amp * Math.sin(2 * Math.PI * freq * i / E.SR) * 0.5 * (1 - Math.cos(2 * Math.PI * i / n));
      return b;
    },
    click(at, buf) { const s = E.ctx.createBufferSource(); s.buffer = buf; s.connect(E.lim); s.start(at); }, // after the song fade: always audible
    // round-trip latency from known emitted clicks: items = [{F (context frame), w (Float32 waveform)}], blocks = mic
    // blocks {f0, d}. Energy matched filter over lags 0..maxL, waveform |xcorr| refine ±5 ms, per-click agreement ±1 ms (own xcorr).
    measureLag(blocks, items, maxL) {
      const SR = E.SR, W = Math.max(...items.map((x) => x.w.length)), F0 = items[0].F, F1 = items[items.length - 1].F;
      const a = F0 - 64, n = F1 + maxL + W + 64 - a, R = new Float32Array(n);
      blocks.forEach((b) => { for (let j = 0; j < b.d.length; j++) { const i = b.f0 + j - a; if (i >= 0 && i < n) R[i] = b.d[j]; } });
      const P = new Float64Array(n + 1); for (let i = 0; i < n; i++) P[i + 1] = P[i] + R[i] * R[i];
      const en = (i, w) => (i < 0 || i + w > n ? 0 : P[i + w] - P[i]);
      const sc = new Float64Array(maxL); let best = 0;
      for (let L = 0; L < maxL; L++) { let e = 0; for (const x of items) e += en(x.F - a + L, x.w.length); sc[L] = e; if (e > sc[best]) best = L; }
      const med = Float64Array.from(sc).sort()[maxL >> 1] || 1e-12;
      let fine = best, fv = -1;
      for (let L = Math.max(0, best - 240); L <= Math.min(maxL - 1, best + 240); L++) { // ±5 ms: the energy peak of a long click can sit 2 ms off (v0.4.5)
        let c = 0; for (const x of items) for (let j = 0; j < x.w.length; j++) { const i = x.F - a + L + j; if (i >= 0 && i < n) c += x.w[j] * R[i]; }
        c = Math.abs(c); if (c > fv) { fv = c; fine = L; }
      }
      let agree = 0;
      for (const x of items) { // per click: its own waveform |xcorr| peak (sharp; the energy peak of a 30 ms click is a
        let bl = 0, bv = -1;     // plateau that wanders ±1 ms with any other sound, v0.4.3)
        for (let L = Math.max(0, fine - 480); L < Math.min(maxL, fine + 480); L++) {
          let c = 0; for (let j = 0; j < x.w.length; j++) { const i = x.F - a + L + j; if (i >= 0 && i < n) c += x.w[j] * R[i]; }
          c = Math.abs(c); if (c > bv) { bv = c; bl = L; }
        }
        if (Math.abs(bl - fine) <= SR / 1000) agree++;
      }
      return { lagF: fine, ms: fine * 1000 / SR, snr: sc[best] / med, agree, n: items.length };
    },
    // take names are numbered across ALL songs (v0.4.3: they restarted at 1 in every song, so takes sent from different
    // songs all read "הקלטה 1"); never reused, a take too short to keep still uses its number
    nextName() { let m = +store.get('harmony.takeN.v1') || 0; REC.takes.forEach((t) => { const x = /(\d+)\s*$/.exec(t.name || ''); if (x) m = Math.max(m, +x[1]); }); store.set('harmony.takeN.v1', m + 1); return 'הקלטה ' + (m + 1); },
    // ---- input level (v0.4.1): live meter, 2 s check on a fresh mic, per-take peak / RMS -> non-destructive gain
    meterShow(on) { $('recMeter').hidden = !on; if (!on) { REC.mLevel = 0; $('recMeterBar').style.transform = 'scaleX(0)'; } },
    meter(d) {
      let p = 0; for (let i = 0; i < d.length; i++) { const a = d[i] < 0 ? -d[i] : d[i]; if (a > p) p = a; }
      REC.mLevel = Math.max(p, (REC.mLevel || 0) * 0.8);
      const x = Math.max(0, Math.min(1, (20 * Math.log10(REC.mLevel + 1e-9) + 60) / 60)); // -60..0 dBFS
      $('recMeterBar').style.transform = 'scaleX(' + x.toFixed(3) + ')';
      if (p >= 0.98) { $('recMeter').classList.add('clip'); clearTimeout(REC.clipT); REC.clipT = setTimeout(() => $('recMeter').classList.remove('clip'), 1000); }
    },
    newStats: () => ({ peak: 0, ss: 0, n: 0, wss: 0, wn: 0, wins: [] }),
    clip(R, v) { // clipping: a run of samples at full scale = one event
      if (v >= 0.99 || v <= -0.99) { R.clipS = (R.clipS || 0) + 1; if (!R.inClip) { R.inClip = true; R.clips = (R.clips || 0) + 1; } } else R.inClip = false;
    },
    acc(st, v) { // one sample into peak / RMS / 50 ms window RMS
      const a = v < 0 ? -v : v; if (a > st.peak) st.peak = a;
      st.ss += v * v; st.n++; st.wss += v * v;
      if (++st.wn === 2400) { st.wins.push(Math.sqrt(st.wss / 2400)); st.wss = 0; st.wn = 0; }
    },
    levels(st) { // peak, RMS, and "loud" = 95th percentile of the 50 ms window RMS (the sung / played parts)
      const w = st.wins.slice().sort((a, b) => a - b);
      return { peak: st.peak, rms: st.n ? Math.sqrt(st.ss / st.n) : 0, loud: w.length ? w[Math.min(w.length - 1, Math.floor(w.length * 0.95))] : 0 };
    },
    db: (x) => (x > 0 ? +(20 * Math.log10(x)).toFixed(1) : -120),
    lr: (x) => '\u2066' + x + '\u2069', // a signed number + unit inside Hebrew text: an LTR isolate keeps "-30 dB" in order
    // playback gain of a take: its loud parts to about -12 dBFS, never past full scale, 1..16 (0..+24 dB). Stored next
    // to the untouched take; "נרמול" in the take's details turns it off.
    autoGain(lv) { return lv.peak > 0 ? +Math.max(1, Math.min(16, 0.98 / lv.peak, 0.25 / Math.max(lv.loud, 1e-9))).toFixed(3) : 1; },
    warn(msg) { const w = $('recWarn'); w.textContent = msg || ''; w.hidden = !msg; },
    async levelCheck(m) {
      ui.status('בדיקת עוצמה: לשיר או לנגן משהו במשך 2 שניות…');
      const st = REC.newStats();
      m.node.port.onmessage = (e) => { const d = e.data.d; REC.meter(d); for (let i = 0; i < d.length; i++) REC.acc(st, d[i]); };
      await new Promise((r) => setTimeout(r, 2000));
      m.node.port.onmessage = null;
      const lv = REC.levels(st); REC.lastCheck = lv;
      lv.dead = lv.peak < 3e-5; // below ~ -90 dBFS: no signal at all (a working mic always has some noise)
      lv.quiet = !lv.dead && lv.peak < 0.03; // under -30 dBFS at its loudest
      if (lv.dead) REC.warn('המיקרופון לא קולט כלום. לבדוק את ההרשאה למיקרופון' + (REC.devs && REC.devs.choice ? ' או לנסות את המיקרופון השני' : '') + '.');
      else if (lv.peak >= 0.98) REC.warn('חזק מדי: הקלט מגיע לקצה (קליפינג). להרחיק את הטלפון מהפה או לשיר חלש יותר.');
      else if (lv.quiet) { REC.low = true; REC.warn('הקלט חלש מאוד (שיא ' + REC.lr(REC.db(lv.peak) + ' dB') + '). לשיר קרוב יותר לטלפון' + (REC.mode !== 'speaker' && !REC.agc() ? ', או להפעיל "הגברה אוטומטית"' : '') + '. ההקלטה תוגבר אוטומטית בהשמעה.'); }
      else REC.warn(null);
      ui.recState();
      return lv;
    },
    audioInfo() { try { return ANDROID && window.Android.audioInfo ? JSON.parse(window.Android.audioInfo()) : null; } catch (e) { return null; } },
    async start() {
      if (REC.on || REC.busy || REC.asking || !E.ready) return;
      if (mix.tempo !== 100) { ui.status('אפשר להקליט רק בקצב 100% (ההשמעה של הקלטות עובדת בכל קצב)'); return; }
      if (!recRoomOk()) return; // (v0.6.0) under FREE_REC_MIN_BYTES free: no take that could be cut mid-way
      if ((!REC.nativeOk() && (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia)) || REC.noDb) { ui.status('ההקלטה לא זמינה במכשיר הזה'); return; }
      if (E.released) revive();
      const ready = E.ctx.state === 'running' ? null : E.ctx.resume(); // inside the tap's gesture
      if (E.playing) pause();
      if (!(await REC.ensureMode())) return;
      REC.fbReason = null;
      if (REC.engine() === 'native') { if ((await REC.startNative(ready)) !== 'fallback') return; REC.fbReason = 'fallback:' + (REC.natError || '?'); REC.lastFallback = REC.fbReason; REC.warn('ההקלטה דרך אנדרואיד לא נפתחה (' + REC.natError + ') — מקליט דרך הדפדפן'); ui.recState(); }
      REC.busy = true; ui.recState();
      let m;
      try { m = await REC.mic(); await ready; } catch (e) { REC.busy = false; ui.recState(); ui.status('אין גישה למיקרופון'); return; }
      REC.meterShow(true);
      if (!m.checked) { // a fresh mic: 2 s level check first
        m.checked = true;
        const lv = await REC.levelCheck(m);
        if (lv.dead) { REC.busy = false; REC.meterShow(false); m.close(); ui.recState(); ui.status('ההקלטה לא התחילה'); return; }
      }
      const ctx = E.ctx, f = E.pausedF >= E.durF - E.SR ? 0 : E.pausedF, L = REC.latencyF(), cal = store.get(REC.latKey());
      const mi = REC.micInfo;
      const take = { id: 't' + Date.now().toString(36) + Math.random().toString(36).slice(2, 6), songId: E.song.id, name: REC.nextName(),
        created: Date.now(), sr: E.SR, startF: f, endF: f, transpose: E.semi || 0, tempo: E.rate, engine: 'webview', engineReason: REC.fbReason || REC.engineReason(), latencyF: L, calibrated: !!cal, calSrc: cal ? cal.src || 'loopback' : null,
        route: REC.routeKey(), routeNative: REC.route(), mode: REC.mode, agcPref: REC.agc(), nudgeMs: 0,
        mic: mi ? { label: mi.label, pref: REC.devs && REC.devs.choice ? REC.micPref() : null, ec: mi.ec, ns: mi.ns, agc: mi.agc, fallback: !!REC.micFallback } : null,
        settings: mi ? mi.settings : null, devices: REC.audioInfo(),
        ctxInfo: { sampleRate: E.SR, baseLatency: ctx.baseLatency, outputLatency: ctx.outputLatency },
        drops: { gaps: 0, gapFrames: 0, at: [], zeroRuns: 0, zeroFrames: 0, queueDropped: 0, writeRetries: 0, blocks: 0 } };
      const A = HV.A, bpm = (A && A.bpm) || 100, beats = (A && parseInt(A.meter, 10)) || 4, beat = 60 / bpm;
      const t0 = ctx.currentTime + 0.25, hi = REC.clickBuf(1500, 30, 0.6), lo = REC.clickBuf(1000, 30, 0.45);
      const items = [];
      for (let i = 0; i < beats; i++) { const F = Math.round((t0 + i * beat) * E.SR), w = i ? lo : hi; REC.click(F / E.SR, w); items.push({ F, w: w.getChannelData(0) }); }
      // the count-in doubles as this take's own latency check when the mic hears it (speaker, or a headphone near the
      // mic): everything is held until it is measured; otherwise the route's calibration (or an estimate) applies
      const maxL = Math.min(Math.round(0.6 * E.SR), Math.round((beat - 0.05) * E.SR));
      REC.cur = { take, m, L, chunks: new Map(), queue: [], run: null, items, maxL, pre: [], measured: false,
        st: REC.newStats(), lastEnd: null, z: 0, zFrom: 0, prevA: 0, pend: new Set(), failed: new Map(), endCtxF: Infinity };
      REC.on = true; REC.busy = false; document.body.classList.add('recording'); ui.recState();
      m.node.port.onmessage = (e) => REC.onBlock(e.data);
      E.playing = true; ui.state();
      stopRun(E.run, 0); E.run = null; // (v0.4.7) the paused run's scheduled sources would play on under the new run: a doubled song
      startAt(f, t0 + beats * beat);
      REC.cur.run = E.run;
      ui.status('מקליט' + (REC.mode === 'speaker' ? ' (מצב רמקול)' : ' (מצב אוזניות)') + '… (⏺ או ⏸ לסיום)');
    },
    onBlock(b) {
      const R = REC.cur; if (!R) return;
      const r = R.run, dr = R.take.drops;
      // dropout check: consecutive blocks must continue each other frame for frame (the worklet starts a new block
      // only when its input skipped frames)
      dr.blocks++;
      if (R.lastEnd != null && b.f0 !== R.lastEnd) {
        dr.gaps++; dr.gapFrames += Math.abs(b.f0 - R.lastEnd);
        if (dr.at.length < 20) dr.at.push([r && r.T0F != null ? R.lastEnd - r.T0F - R.L : null, b.f0 - R.lastEnd]); // [song frame, size]
      }
      R.lastEnd = b.f0 + b.d.length;
      if (b.jit != null) { // the worklet's counters (v0.4.1): absorbed one-quantum stamp slips, re-syncs, input missing
        if (!R.cnt0) R.cnt0 = { jit: b.jit, rs: b.rs, miss: b.miss };
        dr.stampSlips = b.jit - R.cnt0.jit; dr.resyncs = b.rs - R.cnt0.rs; dr.inputMissing = b.miss - R.cnt0.miss;
        if (b.off != null) { dr.offNow = b.off; dr.offMax = Math.max(dr.offMax || 0, Math.abs(b.off)); } // count vs currentFrame (frames)
      }
      REC.meter(b.d);
      if (!R.measured) {
        R.pre.push(b); R.queue.push(b);
        const lastF = R.items[R.items.length - 1].F;
        if (b.f0 + b.d.length < lastF + R.maxL + 2048) return; // wait until the last count-in click + max latency is in
        R.measured = true;
        const res = REC.measureLag(R.pre, R.items, R.maxL); R.pre = null;
        R.take.countIn = { ms: +res.ms.toFixed(2), snr: +res.snr.toFixed(1), agree: res.agree + '/' + res.n };
        // used only when it is believable: >= 20 ms (a real acoustic round trip; ~0 = the click leaking electrically into
        // a headset mic), 3+ clicks agreeing, and never over a calibration in headphones mode (the clap value wins)
        const okCI = res.snr >= 6 && res.agree >= Math.max(3, res.n - 1) && res.ms >= 20 && (REC.mode === 'speaker' || !R.take.calibrated);
        R.take.countIn.used = okCI;
        if (okCI) { R.L = res.lagF; R.take.latencyF = res.lagF; R.take.latSource = 'count-in'; }
        else R.take.latSource = R.take.calibrated ? 'calibration' : 'estimate';
        if (r && r.T0F != null) { const q = R.queue; R.queue = []; q.forEach((x) => REC.write(x, r)); } // (b is in the queue)
        return;
      }
      if (!r || r.T0F == null) { R.queue.push(b); if (R.queue.length > 4000) { R.queue.shift(); dr.queueDropped++; } return; }
      if (R.queue.length) { const q = R.queue; R.queue = []; q.forEach((x) => REC.write(x, r)); }
      REC.write(b, r);
    },
    write(b, r) {
      const R = REC.cur, t = R.take, C = E.Lf, d = b.d, base = b.f0 - r.T0F - R.L - (R.SL != null ? R.SL : (R.SL = t.shiftLatF = Math.round(REC.audLat(r)))), st = R.st, dr = t.drops; // (v0.5.3: − the shifter's delay, frozen at the first block)
      const jEnd = Math.min(d.length, R.endCtxF - b.f0); // nothing captured after ⏺ / ⏸ was pressed
      let last = -1;
      for (let j = 0; j < jEnd; j++) {
        const f = base + j; if (f < t.startF || f >= E.durF) continue;
        const k = Math.floor(f / C); let a = R.chunks.get(k);
        if (!a) { a = new Int16Array(C); R.chunks.set(k, a); }
        const v = d[j]; a[f - k * C] = v >= 1 ? 32767 : v <= -1 ? -32768 : Math.round(v * 32767);
        REC.acc(st, v); REC.clip(R, v);
        // inserted silence: a run of exact zeros that starts abruptly (a real mic is never digitally silent)
        if (v === 0) { if (!R.z++) R.zFrom = R.prevA; } else { if (R.z >= 32 && R.zFrom > 0.002) { dr.zeroRuns++; dr.zeroFrames += R.z; } R.z = 0; R.prevA = v < 0 ? -v : v; }
        last = f;
      }
      if (last < 0) return;
      if (last + 1 > t.endF) t.endF = last + 1;
      R.chunks.forEach((a, k) => { if ((k + 1) * C <= last) { R.chunks.delete(k); REC.putSafe(R, k, a); } }); // complete: to disk
    },
    // chunk writes never lose data: a chunk stays in memory until its write has COMMITTED; a failed write is retried
    // when the take stops (slow writes only queue up: 8 s of mono = 750 KB each)
    putSafe(R, k, a) {
      const p = REC.putChunk(R.take.id, k, a).then(() => { R.pend.delete(p); }, () => { R.pend.delete(p); R.failed.set(k, a); R.take.drops.writeRetries++; });
      R.pend.add(p);
    },
    async stop() {
      if (!REC.on) return;
      if (REC.cur && REC.cur.native) return REC.stopNative();
      const R = REC.cur; REC.on = false; document.body.classList.remove('recording');
      R.endCtxF = Math.round(R.m.ctx.currentTime * E.SR);
      ui.recState();
      R.m.node.port.postMessage('flush'); await new Promise((r) => setTimeout(r, 150)); // the worklet's last partial block
      R.m.node.port.onmessage = null; R.m.close(); REC.cur = null; REC.meterShow(false);
      const t = R.take;
      if (R.z >= 32 && R.zFrom > 0.002) { t.drops.zeroRuns++; t.drops.zeroFrames += R.z; }
      if (t.endF - t.startF < E.SR * 0.5) { ui.status('ההקלטה קצרה מדי — לא נשמרה'); return; } // (nothing of it was ever stored)
      const lv = REC.levels(R.st);
      t.level = { peakDb: REC.db(lv.peak), rmsDb: REC.db(lv.rms), loudDb: REC.db(lv.loud), clips: R.clips || 0, clipSamples: R.clipS || 0 };
      t.gain = REC.autoGain(lv); t.norm = true; t.samples = R.st.n; // samples written (== endF − startF when nothing was lost)
      R.chunks.forEach((a, k) => REC.putSafe(R, k, a)); R.chunks.clear();
      try {
        for (let tries = 0; ; tries++) {
          while (R.pend.size) await Promise.all([...R.pend]);
          if (!R.failed.size) break;
          if (tries >= 4) throw new Error('chunks');
          await new Promise((r) => setTimeout(r, 300 * (tries + 1)));
          const f = [...R.failed]; R.failed.clear(); f.forEach(([k, a]) => REC.putSafe(R, k, a));
        }
        await REC.op('takes', 'readwrite', (st) => st.put(t));
      } catch (e) { ui.status('שמירת ההקלטה נכשלה'); return; }
      REC.takes.push(t); PK.afterTake(t);
      REC.setActive(t, true);
      if (lv.loud < 0.01) REC.low = true;
      const notes = [];
      if (!t.calibrated && t.latSource !== 'count-in') notes.push('כדאי לעשות כיול לסנכרון מדויק');
      if (t.mode === 'speaker') notes.push('הוקלט במצב רמקול');
      if (t.drops.gaps || t.drops.zeroRuns || t.drops.resyncs) notes.push('זוהו קטיעות בקלט (ראו "פרטים")');
      if (t.level.clips) notes.push('חזק מדי: נחתך ' + t.level.clips + ' פעמים (קליפינג) — להרחיק את הטלפון או לשיר חלש יותר');
      if (t.gain >= 2) notes.push('הוגבר אוטומטית ב-' + REC.lr(Math.round(20 * Math.log10(t.gain)) + ' dB'));
      ui.status('נשמרה "' + t.name + '"' + (notes.length ? ' — ' + notes.join(' · ') : ''));
      ui.recState();
    },
    toggle() { if (REC.on) { REC.stop(); if (E.playing) pause(); } else REC.start(); },
    // the take that plays in the "ההקלטה שלי" channel; primary = persisted
    setActive(t, primary) {
      REC.active = t || null;
      if (REC.needsReclean(t) && !REC.cleaning && !REC.on) setTimeout(() => { if (REC.active === t && REC.needsReclean(t)) REC.cleanTake(t); }, 0); // (v0.5.1) an older cleaning: redone with cleaner v2 (raw untouched)
      if (primary && t) store.set(REC.primaryKey(), t.id);
      if (t && !E.song.stems.includes(MINE)) {
        E.song.stems.push(MINE); E.stems.push(stemNode(MINE));
        if (mix.vol.mine == null) { mix.vol.mine = 100; mix.mute.mine = false; }
        ui.addRow(MINE); ui.mix(); applyGains(0);
      }
      if (rows.mine) rows.mine.row.hidden = !t;
      REC.fxApply(); // the channel's effects follow the active take
      pvUpdate(); // (v0.4.8) the pitch view follows the active take (and its nudge)
      vaUpdate(); // (v0.7.0) and the voice analysis / line scores
      // reload the decoded window with the new take (stems re-decode too: simple + rare)
      const at = posF() / E.SR;
      // (v0.4.7: also while playing — seek() keeps the chunks around the playhead, which still held the previous take's
      // audio, so a new take / nudge / switch was not heard until playback left that 16 s window)
      if (E.playing) { evict(1, 0); seek(at); } else { stopRun(E.run, 0); E.run = null; evict(1, 0); E.pausedF = Math.round(at * E.SR); tick(); }
      REC.list();
    },
    async remove(t) {
      try {
        await REC.op('takes', 'readwrite', (st) => st.delete(t.id));
        await REC.op('tchunks', 'readwrite', (st) => st.delete(IDBKeyRange.bound(t.id + ':', t.id + ':￿')));
        await REC.op('tchunks', 'readwrite', (st) => st.delete(vaIdb(t.id))); VA.mem.delete(t.id); // (v0.7.0) its analysis
      } catch (e) { ui.status('המחיקה נכשלה'); return; }
      PK.dropTakes(E.song.id, [t.id]); // (v0.6.0) the user's explicit delete: out of the song's pack too
      REC.takes = REC.takes.filter((x) => x !== t);
      if (REC.active === t) {
        const p = REC.takes[REC.takes.length - 1] || null;
        if (store.get(REC.primaryKey()) === t.id) store.set(REC.primaryKey(), p ? p.id : null);
        REC.setActive(p, !!p);
      } else REC.list();
    },
    // "כיול": speaker mode = loopback (clicks out of the speaker, into the mic); headphones mode = clapping along
    async calibrate() {
      if (REC.on || REC.busy || REC.asking || !E.ready) return;
      if (!REC.nativeOk() && (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia)) { ui.status('ההקלטה לא זמינה במכשיר הזה'); return; }
      if (E.released) revive();
      const ready = E.ctx.state === 'running' ? null : E.ctx.resume();
      if (E.playing) pause();
      if (!(await REC.ensureMode())) return;
      if (REC.engine() === 'native') { try { await ready; } catch (e) { /* later */ } if ((await REC.calNative()) !== 'fallback') return; REC.lastFallback = 'fallback:' + (REC.natError || '?'); REC.warn('ההקלטה דרך אנדרואיד לא נפתחה (' + REC.natError + ') — כיול דרך הדפדפן'); ui.recState(); }
      REC.busy = true; ui.recState();
      let m;
      try { m = await REC.mic(); await ready; } catch (e) { REC.busy = false; ui.recState(); ui.status('אין גישה למיקרופון'); return; }
      try { if (REC.mode === 'speaker') await REC.calLoop(m); else await REC.calClap(m); } finally { REC.busy = false; REC.meterShow(false); ui.recState(); }
    },
    async capture(m, until) { // mic blocks until context time `until`
      const blocks = []; REC.meterShow(true);
      m.node.port.onmessage = (e) => { blocks.push(e.data); REC.meter(e.data.d); };
      while (E.ctx.currentTime < until) await new Promise((r) => setTimeout(r, 50));
      m.node.port.postMessage('flush'); await new Promise((r) => setTimeout(r, 120));
      m.node.port.onmessage = null; m.close();
      return blocks;
    },
    // loopback: 8 short clicks at irregular spacing out, mic in; energy matched filter over 0–600 ms, then waveform
    // cross-correlation ±1 ms; accepted only if >= 5 of the 8 clicks agree within 1 ms
    async calLoop(m) {
      ui.status('כיול: שקט בבקשה…');
      const ctx = E.ctx, SR = E.SR, offs = [0, 0.37, 0.81, 1.19, 1.66, 2.03, 2.47, 2.88], MAXL = Math.round(0.6 * SR);
      const wave = REC.clickBuf(2000, 4, 0.9), W = wave.length, T = wave.getChannelData(0);
      const t0 = ctx.currentTime + 0.4, F = offs.map((o) => Math.round((t0 + o) * SR));
      F.forEach((fr) => REC.click(fr / SR, wave));
      const blocks = await REC.capture(m, (F[F.length - 1] + MAXL + W) / SR + 0.25);
      const res = REC.measureLag(blocks, F.map((fr) => ({ F: fr, w: T })), MAXL);
      REC.lastCal = res;
      if (res.snr < 6 || res.agree < 5) { ui.status('הכיול לא הצליח: הקליקים לא נשמעו ברור במיקרופון. לנסות שוב בשקט'); return; }
      store.set(REC.latKey(), { ms: res.lagF * 1000 / SR, at: Date.now(), src: 'loopback' });
      ui.status('כיול: השהיה ' + Math.round(res.ms) + ' ms (' + ({ bt: 'בלוטות׳', wired: 'אוזניות', speaker: 'רמקול' }[REC.routeKey()] || REC.routeKey()) + ')');
    },
    // clapping along (headphones: the mic can't hear the clicks): 4 low clicks to get the beat, then 8 high clicks at
    // 100 BPM to clap with. Latency = median of (clap onset − click), after dropping outliers. It includes the small,
    // steady habit of clapping a little ahead of (or behind) a beat — the same habit that shapes singing along, so a
    // take lands where it was meant to.
    async calClap(m) {
      ui.status('כיול במחיאות כפיים: 4 קליקים להתכונן, ואז למחוא כף אחת יחד עם כל אחד מ-8 הקליקים הגבוהים');
      const ctx = E.ctx, SR = E.SR, IV = 0.6, LEADN = 4, N = 8;
      const lo = REC.clickBuf(1000, 30, 0.45), hi = REC.clickBuf(1500, 30, 0.6);
      const t0 = ctx.currentTime + 1.5, F = [];
      for (let i = 0; i < LEADN + N; i++) { const fr = Math.round((t0 + i * IV) * SR); REC.click(fr / SR, i < LEADN ? lo : hi); if (i >= LEADN) F.push(fr); }
      const blocks = await REC.capture(m, F[N - 1] / SR + 0.65);
      const res = REC.clapAnalyze(blocks, F, SR);
      REC.lastClap = res;
      if (!res.ok) { ui.status(res.why); return; }
      store.set(REC.latKey(), { ms: res.ms, at: Date.now(), src: 'clap', n: res.used, sd: +res.sd.toFixed(1) });
      ui.status('כיול במחיאות: השהיה ' + REC.lr(Math.round(res.ms) + ' ms') + ' (' + res.used + ' מתוך 8 מחיאות, פיזור ' + REC.lr(Math.round(res.sd) + ' ms') + ')');
    },
    // clap onsets against click frames F (context frames): first difference (claps are broadband; hum and any bleed of
    // the 1–1.5 kHz clicks mostly drop out), 1 ms energy frames, per click the loudest frame in [−120, +480) ms that is
    // >= 16 dB over the median floor, onset = first sample in the 25 ms before it whose |slope| reaches 30 % of the
    // burst's maximum. Outliers: |d − median| > max(12 ms, 3·MAD) (capped 60 ms). Needs 5 of 8, spread <= 35 ms.
    clapAnalyze(blocks, F, SR, raw) { // raw: a residual (native path), may be negative
      const pre = Math.round(0.12 * SR), post = Math.round(0.48 * SR), FR = Math.round(SR / 1000);
      const a = F[0] - pre - 4 * FR, n = F[F.length - 1] + post + 4 * FR - a;
      const x = new Float32Array(n);
      blocks.forEach((b) => { for (let j = 0; j < b.d.length; j++) { const i = b.f0 + j - a; if (i >= 0 && i < n) x[i] = b.d[j]; } });
      const y = new Float32Array(n); for (let i = 1; i < n; i++) y[i] = x[i] - x[i - 1];
      const nf = Math.floor(n / FR), e = new Float64Array(nf);
      for (let k = 0; k < nf; k++) { let s = 0; for (let i = k * FR; i < (k + 1) * FR; i++) s += y[i] * y[i]; e[k] = s; }
      const floor = Float64Array.from(e).sort()[nf >> 1] + 1e-12;
      const d = [];
      for (const Fi of F) {
        const k0 = Math.floor((Fi - pre - a) / FR), k1 = Math.floor((Fi + post - a) / FR);
        let p = k0; for (let k = k0; k < k1; k++) if (e[k] > e[p]) p = k;
        if (e[p] < floor * 40) { d.push(null); continue; }
        let A = 0; for (let i = Math.max(0, (p - 1) * FR); i < Math.min(n, (p + 2) * FR); i++) A = Math.max(A, Math.abs(y[i]));
        let s = Math.max(k0 * FR, (p - 25) * FR);
        while (s < (p + 2) * FR && Math.abs(y[s]) < 0.3 * A) s++;
        d.push(+((s + a - Fi) * 1000 / SR).toFixed(2));
      }
      const med = (v) => { const s = v.slice().sort((p, q) => p - q), h = s.length >> 1; return s.length % 2 ? s[h] : (s[h - 1] + s[h]) / 2; };
      const got = d.filter((v) => v != null);
      if (got.length < 5) return { ok: false, d, why: 'הכיול לא הצליח: נשמעו רק ' + got.length + ' מחיאות מתוך 8. למחוא כף חזק יותר, קרוב לטלפון' };
      const m0 = med(got), lim = Math.min(60, Math.max(12, 3 * 1.4826 * med(got.map((v) => Math.abs(v - m0)))));
      const kept = got.filter((v) => Math.abs(v - m0) <= lim);
      const mean = kept.reduce((p, q) => p + q, 0) / kept.length, sd = Math.sqrt(kept.reduce((p, q) => p + (q - mean) * (q - mean), 0) / kept.length);
      if (kept.length < 5 || sd > 35) return { ok: false, d, sd, why: 'הכיול לא הצליח: המחיאות לא היו אחידות. לנסות שוב, מחיאה אחת בדיוק עם כל קליק' };
      return { ok: true, ms: raw ? med(kept) : Math.max(0, med(kept)), used: kept.length, sd, d };
    },
    ui() {
      REC.modeInit();
      $('recBtn').addEventListener('click', REC.toggle); $('miniRec').addEventListener('click', REC.toggle);
      $('engRetry').addEventListener('click', () => { if (REC.on || REC.busy) return; REC.lastFallback = null; REC.warn(null); ui.recState(); REC.start(); }); // re-attempts the native start
      // (v0.4.9) the manual engine choice is gone (the user: remove the button): a stored choice is deleted once, and noted
      try { const old = localStorage.getItem('harmony.engine.v1'); if (old !== null) { localStorage.removeItem('harmony.engine.v1'); store.set('harmony.engine.migr.v049', { removed: old, at: Date.now() }); console.info('harmony v0.4.9: removed stored engine choice', old); } } catch (e) { /* no storage */ }
      $('recMode').addEventListener('click', () => {
        if (REC.on || REC.busy || REC.asking) return;
        REC.mode = REC.mode === 'headphones' ? 'speaker' : 'headphones'; REC.closeMic();
        store.set(REC.modeKey(), REC.mode); ui.recState();
      });
      $('recCal').addEventListener('click', REC.calibrate);
      $('recVolBack').addEventListener('click', () => REC.volBack()); // (v0.5.1) one tap: the song back to 100 % (or automatic again)
      $('recMic').addEventListener('click', () => {
        if (REC.on || REC.busy) return;
        store.set('harmony.micpref.v1', REC.micPref() === 'phone' ? 'headset' : 'phone'); REC.closeMic(); ui.recState();
      });
      $('recAgc').addEventListener('click', () => {
        if (REC.on || REC.busy) return;
        store.set('harmony.agc.v1', !REC.agc()); REC.closeMic(); ui.recState();
      });
      if (navigator.mediaDevices && navigator.mediaDevices.addEventListener) navigator.mediaDevices.addEventListener('devicechange', () => {
        if (!REC.on && !REC.busy) { REC.closeMic(); if (!REC.asking) REC.modeInit(); ui.recState(); }
        REC.scanDevs();
      });
      REC.scanDevs();
      // fine-tune (v0.4.5: buttons only, no slider): a tap = exactly 1 ms; held: repeats after 0.4 s every 80 ms, 5 ms per
      // step after 0.6 s, 10 ms after 1.5 s; clamped to ±500 ms. Shown at once; saved (t.nudgeMs) and the take reloaded
      // when the finger lifts (one reload per press). "איפוס" = 0.
      const showNudge = (v) => { REC.nudgeV = v; $('nudgeVal').textContent = (v > 0 ? '+' : '') + v + ' ms'; };
      const commitNudge = () => {
        const t = REC.active; if (!t) return; const v = REC.nudgeV || 0; if (v === (t.nudgeMs || 0)) return;
        t.nudgeMs = v; REC.op('takes', 'readwrite', (st) => st.put(t)).catch(() => {}); REC.setActive(t, false);
      };
      [['nudgeEarly', -1], ['nudgeLate', 1]].forEach(([id, dir]) => {
        const b = $(id); let rep = 0, t0 = 0, down = false;
        const step = (n) => { if (!REC.active) return; showNudge(Math.max(-500, Math.min(500, (REC.nudgeV || 0) + dir * n))); };
        const up = () => { if (!down) return; down = false; clearTimeout(rep); clearInterval(rep); commitNudge(); };
        b.addEventListener('pointerdown', (e) => {
          if (!REC.active || e.button > 0) return; down = true; t0 = performance.now(); step(1);
          try { b.setPointerCapture(e.pointerId); } catch (x) { /* noop */ }
          rep = setTimeout(() => { rep = setInterval(() => { const h = performance.now() - t0; step(h > 1500 ? 10 : h > 600 ? 5 : 1); }, 80); }, 400);
        });
        ['pointerup', 'pointercancel', 'lostpointercapture'].forEach((ev) => b.addEventListener(ev, up));
        b.addEventListener('keydown', (e) => { if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); down = true; step(1); up(); } }); // keyboard / switch access
        b.addEventListener('contextmenu', (e) => e.preventDefault()); // a long press must not open a menu
      });
      $('nudgeReset').addEventListener('click', () => { if (!REC.active) return; showNudge(0); commitNudge(); });
      $('nudgeListen').addEventListener('click', () => { const t = REC.active; if (!t) return; seek(Math.max(0, t.startF / E.SR - 1)); if (!E.playing) play(); });
      ['recBtn', 'miniRec', 'recMode', 'recCal'].forEach((id) => { $(id).disabled = false; });
      ui.recState(); REC.list();
    },
    // ---- native capture (v0.4.2, Android): AudioRecord on its own thread into a file (NativeRec.kt) — no
    // getUserMedia, so Android never enters its voice-call audio mode and page jank can't drop samples. Mapping of a
    // recorded sample k to the song, all on CLOCK_MONOTONIC (ms):
    //   capture time  t(k) = A + (k + lost(k)) · 1000/SR          (A = nanoTime − framePosition·1000/SR from AudioRecord's
    //                 timestamps; framePosition is in the app's reading order, a drop shows as a step in A)
    //   page clock    perf = t − off                              (off = monoMs − performance.now, best of 15 round trips)
    //   heard frame   ctxF = q + perf · SR/1000                   (q = median of contextTime·SR − performanceTime·SR/1000
    //                 over AudioContext.getOutputTimestamp: the context frame coming out of the phone at that moment)
    //   song frame    f = ctxF − T0F − R                          (R = residual from "כיול" or the take's own count-in:
    //                 what the clocks don't know — adapter / headphone delay, the habit of singing a little ahead)
    // So ctxF(k) = K + k + lost(k) with one constant K per take; a frame drop reported natively leaves a hole of exactly
    // its length (sync after it is kept). Clock drift (ppm) is measured and shown, not corrected (±2 ms over 3 min at 10 ppm).
    nativeOk: () => ANDROID && !!window.Android.recStart,
    engine() { return REC.nativeOk() ? 'native' : 'webview'; }, // v0.5.0: speaker mode records natively too (the song is removed after the stop)
    // (v0.4.9) WHY a take is (not) recorded through Android's own capture — stored with every take, shown in פרטים
    engineReason() {
      if (!ANDROID) return 'no-bridge';
      if (!window.Android.recStart) return 'no-recStart';
      return 'native';
    },
    reasonHe: (r) => (r === 'native' ? '' : r === 'speaker-mode' ? 'מצב רמקול' : r === 'pref:webview' ? 'נבחר ידנית (גרסה ישנה)' : r === 'no-bridge' || r === 'no-recStart' ? 'אין גישה להקלטה של אנדרואיד'
      : /^fallback:/.test(r || '') ? 'ההקלטה דרך אנדרואיד לא נפתחה: ' + r.slice(9) : r || 'לא ידוע'),
    // headphones mode records natively; when the native start failed (fallback), a warning stays until a native take
    // succeeds, with "לנסות שוב" (re-attempts the native start). Speaker mode: WebView by design, no warning.
    engWarn() {
      const w = $('engWarn'); if (!w) return;
      const fb = REC.lastFallback, show = ANDROID && !!REC.mode && !REC.on && !!fb;
      w.hidden = !show; if (!show) return;
      $('engWarnText').textContent = '⚠️ ההקלטה דרך אנדרואיד לא נפתחה (' + fb.slice(9) + ') — ההקלטה עברה דרך הדפדפן, באיכות נמוכה יותר';
    },
    natChoice() { try { const s = window.Android.audioInputs(); return /builtin/.test(s) && /wired|usb/.test(s); } catch (e) { return false; } },
    rawPref: () => store.get('harmony.raw.v1') === true, // UNPROCESSED only by opt-in: vc16's VOICE_RECOGNITION is the one proven on the phone
    natPerm() {
      const A = window.Android; if (A.micGranted()) return Promise.resolve(true);
      return new Promise((res) => { window.__harmonyMic = (ok) => { window.__harmonyMic = null; res(!!ok); }; A.askMic(); });
    },
    clockSync() {
      const A = window.Android; let best = null;
      for (let i = 0; i < 15; i++) { const p0 = performance.now(), m = A.monoMs(), p1 = performance.now(); if (!best || p1 - p0 < best.rtt) best = { rtt: p1 - p0, off: m - (p0 + p1) / 2 }; }
      return best;
    },
    natBegin(kind) {
      const A = window.Android, id = kind + Date.now().toString(36) + Math.random().toString(36).slice(2, 6);
      let info; try { info = JSON.parse(A.recStart(id, E.SR, REC.mode || 'headphones', REC.natChoice() ? REC.micPref() : 'phone', REC.rawPref())); } catch (e) { info = { ok: false, error: String(e) }; }
      if (!info.ok) { REC.natError = info.error; return null; }
      const s = { id, info, clk0: REC.clockSync(), outTs: [], curTs: [], peakMax: 0, peaks: [] };
      const poll = () => {
        try { const o = E.ctx.getOutputTimestamp(); if (o.performanceTime > 0 && o.contextTime > 0) s.outTs.push([o.contextTime, o.performanceTime]); } catch (e) { /* none */ }
        if (E.ctx.state === 'running') s.curTs.push([E.ctx.currentTime - (E.ctx.outputLatency || 0) - (E.ctx.baseLatency || 0), performance.now()]); // heard ≈ rendered − latency
      };
      s.tsT = setInterval(poll, 200);
      s.mT = setInterval(() => { const p = A.recPeak() / 32768; s.peakMax = Math.max(s.peakMax, p); s.peaks.push(p); REC.meter([p]); REC.clipTick(s, A); }, 100);
      REC.meterShow(true);
      return s;
    },
    async natEnd(s) {
      clearInterval(s.tsT); clearInterval(s.mT);
      const A = window.Android, SR = E.SR, monoStop = A.monoMs(), perfStop = performance.now(), ctxStop = E.ctx.currentTime, st = JSON.parse(A.recStop()), clk1 = REC.clockSync();
      let pcm = new Int16Array(0);
      try { const r = await fetch('/rec/' + s.id + '.pcm'); if (r.ok) pcm = new Int16Array(await r.arrayBuffer()); } catch (e) { /* stays empty */ }
      try { A.recDelete(s.id); } catch (e) { /* noop */ }
      const med = (v) => { const a = v.slice().sort((x, y) => x - y), h = a.length >> 1; return a.length ? (a.length % 2 ? a[h] : (a[h - 1] + a[h]) / 2) : NaN; };
      // AudioRecord timestamps: framePosition counts frames in the app's own reading order (AOSP shifts the server
      // positions into it), so frame k was captured at r + k·1000/SR with r = nanoTime/1e6 − framePosition·1000/SR,
      // constant while nothing is dropped. Dropped frames never reach the app: time runs on without them, so r steps UP
      // by their duration. A step > 10 ms, confirmed by the median of the next 5 timestamps, is a drop at that frame.
      const ts = st.ts || [], rr = ts.map((x) => x[2] / 1e6 - x[1] * 1000 / SR), lostAt = [];
      let rBase = rr.length ? med(rr.slice(0, Math.min(5, rr.length))) : 0, lostNow = 0; const cuts = [];
      for (let i = 1; i + 5 <= rr.length; i++) {
        const after = med(rr.slice(i, i + 5)), l = Math.round((after - rBase) * SR / 1000);
        if (l - lostNow > SR / 100 && rr[i] - rr[i - 1] > 5) { // the system drops once the buffer is full: framesRead + capacity
          lostNow = l; lostAt.push([Math.min(ts[i][1], Math.max(ts[i - 1][1], ts[i - 1][0] + (st.bufferFrames || 0))), l]); cuts.push(i);
        }
      }
      // capture clock steadiness: spread of A within each stretch between drops (drift / jitter of the timestamps)
      let aSpreadMs = 0; [0, ...cuts, rr.length].forEach((c, j, arr) => { if (j === arr.length - 1) return; const seg = rr.slice(j ? c + 3 : c, arr[j + 1]); /* after a drop the HAL holds framePosition for a moment: skip that transient */ if (seg.length > 1) aSpreadMs = Math.max(aSpreadMs, Math.max(...seg) - Math.min(...seg)); });
      const bl = ts.map((x) => x[1] - x[0]), maxBacklogMs = bl.length ? +((Math.max(...bl) - Math.min(...bl)) * 1000 / SR).toFixed(1) : null; // buffering seen (diagnostic)
      if (!s.outTs.length) { const o = E.ctx; s.outTs.push([o.currentTime - (o.outputLatency || 0) - (o.baseLatency || 0), performance.now()]); s.outFallback = true; } // no output timestamps: estimate
      // output clock: getOutputTimestamp when it is steady (spread p10–p90 < 15 ms), else currentTime − output latency
      // (both medians over the whole take; the choice and both spreads go into the take's details)
      const qOf = (a) => a.map(([ct, pt]) => ct * SR - pt * SR / 1000), spread = (a) => { if (a.length < 5) return Infinity; const b = a.slice().sort((x, y) => x - y); return (b[Math.floor(b.length * 0.9)] - b[Math.floor(b.length * 0.1)]) * 1000 / SR; };
      const qo = qOf(s.outTs), qc = qOf(s.curTs), so = spread(qo), sc = spread(qc), useOut = so < 15 || so <= sc;
      const Am = rBase, q = med(useOut ? qo : qc), outClock = useOut ? 'outputTimestamp' : 'currentTime'; // capture clock: frame k (+ drops) at Am + k·1000/SR
      const qSpreadMs = { outputTimestamp: Number.isFinite(so) ? +so.toFixed(2) : null, currentTime: Number.isFinite(sc) ? +sc.toFixed(2) : null };
      const off = (s.clk0.off + clk1.off) / 2, K = q + (Am - off) * SR / 1000;
      const lost = (k) => { let l = 0; for (const [kk, cum] of lostAt) { if (kk <= k) l = cum; else break; } return l; };
      const span = (a, b, n) => (a.length > 1 ? n(a[a.length - 1]) - n(a[0]) : 0);
      const inDrift = ts.length > 1 ? ((span(ts, 0, (x) => x[1]) / SR) / (span(ts, 0, (x) => x[2]) / 1e9) - 1) * 1e6 : null;
      const outDrift = s.outTs.length > 1 ? ((span(s.outTs, 0, (x) => x[0])) / (span(s.outTs, 0, (x) => x[1]) / 1000) - 1) * 1e6 : null;
      const diag = { source: st.source, sourcesFailed: st.sourcesFailed, effects: st.effects, audioMode: [st.modeBefore, st.modeAtStart, st.modeAtStop].join(' / '), preferred: st.preferred, preferredSet: st.preferredSet, routed: st.routed || null, unprocessedSupported: st.unprocessedSupported,
        frames: st.frames, pcmFrames: pcm.length, readErrors: st.readErrors, maxBacklogMs, aSpreadMs: +aSpreadMs.toFixed(3), outClock, outSpreadMs: qSpreadMs, lost: lostAt.length ? lostAt[lostAt.length - 1][1] : 0, lostAt, timestamps: ts.length, outTimestamps: s.outTs.length,
        outFallback: !!s.outFallback, clockRttMs: +Math.max(s.clk0.rtt, clk1.rtt).toFixed(3), clockStepMs: +(clk1.off - s.clk0.off).toFixed(3),
        // sanity of the clocks: newest captured sample vs the moment of ⏹ (expect a few tens of ms: the capture buffer),
        // and the heard frame vs the context clock at ⏹ (expect about the output latency)
        captureLagMs: ts.length ? +(monoStop - (Am + (st.frames - 1 + lostNow) * 1000 / SR)).toFixed(1) : null,
        outputLagMs: +((ctxStop * SR - (q + perfStop * SR / 1000)) * 1000 / SR).toFixed(1),
        inDriftPpm: inDrift == null ? null : +inDrift.toFixed(1), outDriftPpm: outDrift == null ? null : +outDrift.toFixed(1), K: +K.toFixed(1), peak: +s.peakMax.toFixed(4),
        elapsedMs: st.elapsedMs != null ? +(+st.elapsedMs).toFixed(1) : null, joinTimedOut: !!st.joinTimedOut, threadAlive: !!st.threadAlive, clipSamples: st.clips != null ? st.clips : null };
      // (v0.5.1) truncation: the newest sample IN THE FILE vs the moment of ⏹ (normally a few ms: what was still in the
      // capture buffer); without timestamps, the recorder's own elapsed time vs the file's length (minus start-up)
      const fileEndMs = ts.length ? monoStop - (Am + (pcm.length - 1 + lostNow) * 1000 / SR) : st.elapsedMs != null ? st.elapsedMs - (pcm.length + lostNow) * 1000 / SR - 300 : 0;
      diag.truncatedMs = Math.max(0, Math.round(fileEndMs));
      REC.meterShow(false);
      return { pcm, K, lost, diag, ok: ts.length > 0 && pcm.length > 0 };
    },
    // a stretch of the native recording as worklet-style blocks on the context-frame axis (for measureLag / clapAnalyze)
    natBlocks(n, from, to, shift = 0) {
      const out = []; let k = Math.max(0, from);
      while (k < Math.min(to, n.pcm.length)) {
        const l0 = n.lost(k), f0 = Math.round(n.K) + k + l0 + shift; let e = Math.min(to, n.pcm.length, k + 2048);
        for (let j = k + 1; j < e; j++) if (n.lost(j) !== l0) { e = j; break; }
        const d = new Float32Array(e - k); for (let j = k; j < e; j++) d[j - k] = n.pcm[j] / 32768;
        out.push({ f0, d }); k = e;
      }
      return out;
    },
    // (v0.5.3) what the stems' path adds before the output while recording (transpose ≠ 0: the shifter), in frames: the
    // mean over all of the take's splices once measured (the best constant for a voice that follows the music), else
    // the first measurement, else the prior; + the path's equalising delay
    audLat(r) { if (!r || r.pA === 1 || r.pA == null) return r ? r.dA || 0 : 0; const m = r.latAll != null ? r.latAll : r.latAm != null ? r.latAm : r.latA; return m + (r.dA || 0); },
    natKFor(n, ctxF) { return Math.round(ctxF - Math.round(n.K)); }, // sample index heard at context frame ctxF (ignoring drops)
    // ---- (v0.5.1) speaker mode: the app's own output level (E.vol, before the reference tap). Per route: { g, by, override }
    //   by 'check' = set by the 2 s check (recomputed each take), 'clip' = lowered during a take (only goes lower until
    //   "להחזיר עוצמה"), override = the user wants 100 %: nothing lowers it automatically (the overlay still warns)
    VOL_LIMIT_DB: -12, VOL_HEAD_DB: 6, VOL_FLOOR: 0.3, VOL_STEP_DB: -3,
    volKey: () => 'harmony.spkvol.v1.' + REC.routeKey(),
    vol() { const v = store.get(REC.volKey()); return v && typeof v === 'object' && v.g > 0 ? v : { g: 1, by: null, override: false }; },
    volSet(v) { store.set(REC.volKey(), v); ui.recState(); },
    volApply(g) { REC.volNow = g; if (!E.vol) return; const c = E.ctx; E.vol.gain.cancelScheduledValues(c.currentTime); E.vol.gain.setTargetAtTime(g, c.currentTime, 0.02); },
    pct: (g) => REC.lr(Math.round(g * 100) + '%'), // (bidi-isolated, like the dB values)
    volBack() { // "להחזיר עוצמה" (and back to automatic)
      const v = REC.vol();
      if (v.override) { REC.volSet({ g: 1, by: null, override: false }); ui.status('הנמכה אוטומטית פועלת שוב (מההקלטה הבאה)'); return; }
      REC.volSet({ g: 1, by: null, override: true });
      if (REC.on && REC.cur && REC.cur.native && REC.mode === 'speaker') { const t = REC.cur.take, from = REC.volNow || 1; REC.volApply(1); (t.gainSteps = t.gainSteps || []).push({ sec: +(posF() / E.SR).toFixed(2), from: +from.toFixed(3), to: 1, by: 'user' }); }
      ui.status('עוצמת השיר הוחזרה ל-100% (בלי הנמכה אוטומטית)');
    },
    // the loudest 2 s of the song (songs/<id>/melody.json: loudSec, computed offline from the full mix); else the 2 s before the start
    async loudSpan(f00) {
      try { if (!REC.loudOf || REC.loudOf.id !== E.song.id) { const r = await fetch(E.base + 'melody.json'); const j = r.ok ? await r.json() : null; REC.loudOf = { id: E.song.id, sec: j && Array.isArray(j.loudSec) ? j.loudSec : null }; } } catch (e) { REC.loudOf = { id: E.song.id, sec: null }; }
      const l = REC.loudOf.sec; if (l && l[1] > l[0]) return { t0: l[0], t1: l[1], src: 'loudest' };
      const t1 = Math.max(2, f00 / E.SR); return { t0: t1 - 2, t1, src: 'before-start' };
    },
    // (v0.5.1) clipping during a speaker take: ≥ 20 full-scale samples within 0.5 s = one event (at most one per second):
    // the big overlay, and the master level −3 dB (floor 30 %), logged in the take; the reference follows (tap after E.vol)
    clipTick(s, A) {
      if (!A.recClips) return; let c; try { c = +A.recClips() || 0; } catch (e) { return; }
      const now = performance.now(), h = s.clipH || (s.clipH = []); h.push([now, c]);
      while (h.length > 1 && now - h[1][0] >= 500) h.shift();
      const R = REC.cur; if (!REC.on || !R || !R.native || R.s !== s || REC.mode !== 'speaker') return;
      const d = c - h[0][1]; if (d < 20 || now - (s.lastStep || 0) < 1000) return;
      s.lastStep = now; s.clipH = [[now, c]];
      const t = R.take, v = REC.vol(), from = REC.volNow || 1, to = v.override ? from : Math.max(REC.VOL_FLOOR, from * Math.pow(10, REC.VOL_STEP_DB / 20)), step = to < from - 1e-3;
      if (step) { REC.volApply(to); REC.volSet({ g: +to.toFixed(3), by: 'clip', override: false }); }
      const log = t.gainSteps = t.gainSteps || []; if (log.length < 60) log.push({ sec: +(posF() / E.SR).toFixed(2), from: +from.toFixed(3), to: +to.toFixed(3), clips: d, by: step ? 'clip' : v.override ? 'override' : 'floor' });
      REC.overlay(step ? '🔊 חזק מדי — מנמיכה את השיר' : '🔊 חזק מדי — להנמיך את עוצמת הטלפון');
    },
    overlay(msg) {
      const o = $('clipOverlay'); if (!o) return; $('clipOverlayText').textContent = msg; o.hidden = false; o.classList.remove('pulse'); void o.offsetWidth; o.classList.add('pulse');
      clearTimeout(REC.ovT); REC.ovT = setTimeout(() => { o.hidden = true; }, 2500);
    },
    // ---- speaker-mode cleaning (v0.5.0): the reference is the app's own output, tapped on the same audio clock
    async refTap() {
      try {
        await REC.ensureModule();
        // (v0.5.2) STEREO: the phone plays left / right from two speakers at different distances; the cleaner needs both
        const ctx = E.ctx, node = new AudioWorkletNode(ctx, 'harmony-rec', { numberOfInputs: 1, numberOfOutputs: 1, outputChannelCount: [1], channelCount: 2, channelCountMode: 'explicit', processorOptions: { stereo: true } });
        const sink = ctx.createGain(); sink.gain.value = 0; E.vol.connect(node); node.connect(sink); sink.connect(ctx.destination);
        const blocks = []; node.port.onmessage = (e) => { if (e.data && e.data.d) blocks.push([e.data.f0, e.data.d, e.data.d2 || null]); };
        return { stop() { try { node.port.postMessage('flush'); } catch (e) { /* gone */ } try { E.vol.disconnect(node); node.disconnect(); sink.disconnect(); } catch (e) { /* gone */ } node.port.onmessage = null; return blocks; } };
      } catch (e) { return null; }
    },
    async putRef(t, blocks, T0F) { // (v0.5.2) stereo: left -> <id>:r, right -> <id>:r2 (t.refCh = 2); older takes: mono in <id>:r
      const C = E.Lf, st = blocks.some((b) => b[2]), maps = st ? [new Map(), new Map()] : [new Map()];
      const q = (v) => (v >= 1 ? 32767 : v <= -1 ? -32768 : Math.round(v * 32767));
      for (const [f0, d, d2] of blocks) for (let i = 0; i < d.length; i++) {
        const f = f0 + i - T0F; if (f < t.startF || f >= t.endF) continue;
        const k = Math.floor(f / C), j = f - k * C;
        for (let c = 0; c < maps.length; c++) { let a = maps[c].get(k); if (!a) { a = new Int16Array(C); maps[c].set(k, a); } a[j] = q(c ? (d2 || d)[i] : d[i]); }
      }
      for (const [k, a] of maps[0]) await REC.putChunk(t.id + ':r', k, a);
      if (st) for (const [k, a] of maps[1]) await REC.putChunk(t.id + ':r2', k, a);
      t.refCh = st ? 2 : 1;
    },
    // (v0.5.2) older speaker takes stored a MONO reference (the tap averaged L / R). Rebuild a stereo one from the song's
    // own stems: per 8 s chunk, the stem gains that best explain the stored mono (least squares), a 10 ms gain envelope
    // (the limiter), then the same gains on left / right. Used only when the rebuilt mono matches the stored one
    // (fitDb >= 25 dB: same mix, nothing else playing); otherwise the take stays on the mono reference.
    async stereoFromStems(t, mono, onProg) {
      const C = E.Lf, n = t.endF - t.startF, L = new Float32Array(n), R = new Float32Array(n), ids = E.song.stems.filter((s) => !s.take).map((s) => s.id), S = ids.length;
      let eRef = 0, eErr = 0; const k0 = Math.floor(t.startF / C), k1 = Math.ceil(t.endF / C);
      const dec = async (k) => { const kk = String(k).padStart(2, '0'); return Promise.all(ids.map((id) => fetchBuf(`${id}-${kk}.${E.song.ext}`).then(decode))); };
      // the stored reference was tapped after the limiter, which delays by its look-ahead (6 ms in Chromium): find that
      // lag once (the cleaner's own GCC-PHAT, on the loudest whole chunk of the take), then fit with it
      let lag = 0, cache = null;
      { let kBest = -1, eBest = 0; for (let k = k0; k < k1; k++) { const f0 = Math.max(t.startF, k * C), f1 = Math.min(t.endF, (k + 1) * C); let e = 0; for (let f = f0; f < f1; f += 16) { const v = mono[f - t.startF]; e += v * v; } if (f1 - f0 > E.SR * 4 && e > eBest) { eBest = e; kBest = k; } }
        if (kBest >= 0 && window.HarmonyClean) { const bufs = await dec(kBest); cache = { k: kBest, bufs }; const sF = Math.max(0, kBest * C - E.Mf), f0 = Math.max(t.startF, kBest * C), f1 = Math.min(t.endF, (kBest + 1) * C);
          const sm = new Float32Array(f1 - f0); for (const b of bufs) { const l = b.getChannelData(0), r = b.numberOfChannels > 1 ? b.getChannelData(1) : l; for (let f = f0; f < f1; f++) { const i = f - sF + E.D; if (i >= 0 && i < l.length) sm[f - f0] += 0.5 * (l[i] + r[i]); } }
          lag = window.HarmonyClean.align(sm, mono.subarray(f0 - t.startF, f1 - t.startF), E.SR).lag; } }
      for (let k = k0; k < k1; k++) {
        const bufs = cache && cache.k === k ? cache.bufs : await dec(k);
        const sF = Math.max(0, k * C - E.Mf), f0 = Math.max(t.startF, k * C), f1 = Math.min(t.endF, (k + 1) * C), m = f1 - f0; if (m <= 0) continue;
        const chL = bufs.map((b) => b.getChannelData(0)), chR = bufs.map((b) => (b.numberOfChannels > 1 ? b.getChannelData(1) : b.getChannelData(0)));
        const ix = (f) => f - lag - sF + E.D, at = (a, f) => { const i = ix(f); return i >= 0 && i < a.length ? a[i] : 0; }; // (a lag reaching into the previous chunk's margin: the margin covers it)
        const Am = new Float64Array(S * S), bv = new Float64Array(S), ms = new Float64Array(S);
        for (let f = f0; f < f1; f++) { const y = mono[f - t.startF]; for (let s = 0; s < S; s++) ms[s] = 0.5 * (at(chL[s], f) + at(chR[s], f));
          for (let s = 0; s < S; s++) { bv[s] += ms[s] * y; for (let u = s; u < S; u++) Am[s * S + u] += ms[s] * ms[u]; } }
        let tr = 0; for (let s = 0; s < S; s++) { for (let u = 0; u < s; u++) Am[s * S + u] = Am[u * S + s]; tr += Am[s * S + s]; }
        for (let s = 0; s < S; s++) Am[s * S + s] += 1e-9 * tr + 1e-12;
        const g = REC.solve(Am, bv, S);
        const W = 480; for (let a = f0; a < f1; a += W) { const b = Math.min(f1, a + W); let uu = 0, uv = 0;
          for (let f = a; f < b; f++) { let lf = 0, rf = 0; for (let s = 0; s < S; s++) { lf += g[s] * at(chL[s], f); rf += g[s] * at(chR[s], f); } L[f - t.startF] = lf; R[f - t.startF] = rf; const u = 0.5 * (lf + rf); uu += u * u; uv += u * mono[f - t.startF]; }
          const env = uu > 1e-12 ? Math.max(0, Math.min(2, uv / uu)) : 1;
          for (let f = a; f < b; f++) { const i = f - t.startF; L[i] *= env; R[i] *= env; const y = mono[i], e = y - 0.5 * (L[i] + R[i]); eRef += y * y; eErr += e * e; } }
        if (onProg) onProg((k - k0 + 1) / (k1 - k0));
      }
      return { L, R, lag, fitDb: eErr > 0 ? +(10 * Math.log10(eRef / eErr)).toFixed(1) : 99 };
    },
    solve(A, b, S) { // Gaussian elimination with partial pivoting (S <= 8)
      const M = Array.from({ length: S }, (_, i) => [...A.subarray(i * S, i * S + S), b[i]]);
      for (let c = 0; c < S; c++) { let p = c; for (let r = c + 1; r < S; r++) if (Math.abs(M[r][c]) > Math.abs(M[p][c])) p = r; [M[c], M[p]] = [M[p], M[c]];
        const d = M[c][c] || 1e-30; for (let r = c + 1; r < S; r++) { const f = M[r][c] / d; for (let j = c; j <= S; j++) M[r][j] -= f * M[c][j]; } }
      const x = new Float64Array(S); for (let r = S - 1; r >= 0; r--) { let v = M[r][S]; for (let j = r + 1; j < S; j++) v -= M[r][j] * x[j]; x[r] = v / (M[r][r] || 1e-30); }
      return x;
    },
    async trackOf(id, t) { // Float32 of a stored track (raw / ref / clean) for song frames [startF, endF)
      const C = E.Lf, n = t.endF - t.startF, out = new Float32Array(n);
      for (let k = Math.floor(t.startF / C); k * C < t.endF; k++) { const d = await REC.getChunk(id, k); if (!d) continue; const base = k * C;
        for (let f = Math.max(t.startF, base); f < Math.min(t.endF, base + C); f++) out[f - t.startF] = d[f - base] / 32768; }
      return out;
    },
    async cleanWorker() { if (!REC.cw) { const src = await (await fetch('clean.js')).text(); REC.cw = new Worker(URL.createObjectURL(new Blob([src], { type: 'application/javascript' }))); } return REC.cw; },
    needsReclean: (t) => !!(t && t.hasRef && (!t.clean || (t.clean.v || 1) < 3)), // (v0.5.2: v3 = stereo-capable)
    async recleanOld() { // the active take first, then the others; one at a time, never during a recording
      const q = REC.takes.filter(REC.needsReclean).sort((a, b) => (b === REC.active) - (a === REC.active));
      for (const t of q) { while (REC.cleaning || REC.on || REC.busy) await new Promise((r) => setTimeout(r, 1000)); if (REC.needsReclean(t) && REC.takes.includes(t)) await REC.cleanTake(t); }
    },
    async cleanTake(t) {
      if (REC.cleaning) return; REC.cleaning = t.id; const t0 = performance.now();
      const show = (f) => { ui.status('מנקה את השיר מההקלטה… ' + Math.round(f * 100) + '%'); };
      try {
        show(0);
        let x = await REC.trackOf(t.id + ':r', t), xR = null, refSrc = 'mono', fitDb = null; const y = await REC.trackOf(t.id, t);
        if (t.refCh === 2) { xR = await REC.trackOf(t.id + ':r2', t); refSrc = 'stereo'; }
        else if (!t.transpose && !(t.tempo && t.tempo !== 1)) { // (v0.5.2) an older take (always 100 %, original key): try a stereo reference rebuilt from the stems
          try { ui.status('מכין את השיר לניקוי…'); const st = await REC.stereoFromStems(t, x, (f) => ui.status('מכין את השיר לניקוי… ' + Math.round(f * 100) + '%')); fitDb = st.fitDb; t.refLag = st.lag; if (st.fitDb >= 25) { x = st.L; xR = st.R; refSrc = 'stems'; } } catch (e) { fitDb = null; }
        }
        let res;
        try {
          const w = await REC.cleanWorker(), id = Date.now();
          res = await new Promise((ok, bad) => {
            const on = (e) => { const m = e.data; if (!m || m.id !== id) return; if (m.prog != null) { show(m.prog); return; } w.removeEventListener('message', on); if (m.error) bad(new Error(m.error)); else ok(m); };
            w.addEventListener('message', on); w.addEventListener('error', (e) => { REC.cw = null; bad(e); }, { once: true });
            w.postMessage({ id, x, xR, y, sr: E.SR }, xR ? [x.buffer, xR.buffer, y.buffer] : [x.buffer, y.buffer]);
          });
        } catch (e) { await new Promise((q) => setTimeout(q, 30)); const st2 = t.refCh === 2, r = window.HarmonyClean.clean(await REC.trackOf(t.id + ':r', t), await REC.trackOf(t.id, t), E.SR, st2 ? { xR: await REC.trackOf(t.id + ':r2', t) } : {}); res = { out: r.out, stats: r.stats, mono: !st2 }; } // (no Worker: on this thread; a rebuilt stereo reference is not redone here)
        const C = E.Lf, o = res.out;
        for (let k = Math.floor(t.startF / C); k * C < t.endF; k++) { const a = new Int16Array(C), base = k * C;
          for (let f = Math.max(t.startF, base); f < Math.min(t.endF, base + C); f++) { const v = o[f - t.startF]; a[f - base] = v >= 1 ? 32767 : v <= -1 ? -32768 : Math.round(v * 32767); }
          await REC.putChunk(t.id + ':c', k, a); }
        t.clean = { ...res.stats, v: 3, refSrc: res.mono ? 'mono' : refSrc, fitDb, wallMs: Math.round(performance.now() - t0) };
        await REC.op('takes', 'readwrite', (x2) => x2.put(t));
        ui.status('השיר הוסר מההקלטה (' + REC.lr('−' + Math.max(0, Math.round(t.clean.reductionDb || 0)) + ' dB') + ') · 🧹 = ההקלטה הנקייה');
        if (REC.active === t) REC.setActive(t, false); else REC.list();
      } catch (e) { ui.status('ניקוי השיר נכשל — ההקלטה המקורית נשמרה'); t.clean = { v: 3, error: String(e && e.message || e) }; REC.op('takes', 'readwrite', (x2) => x2.put(t)).catch(() => {}); }
      finally { REC.cleaning = null; }
    },
    async startNative(ready) {
      REC.busy = true; ui.recState();
      if (!(await REC.natPerm())) { REC.busy = false; ui.recState(); ui.status('אין הרשאה למיקרופון'); return 'done'; }
      try { await ready; } catch (e) { /* resumed later */ }
      const s = REC.natBegin('t'); if (!s) { REC.busy = false; ui.recState(); return 'fallback'; }
      const spk = REC.mode === 'speaker'; let bleed = null;
      if (spk) { // (v0.5.1) speaker mode, every take: the song's loudest 2 s, how loud they reach the mic -> the app's level
        const f00 = E.pausedF, span = await REC.loudSpan(f00), v = REC.vol(), g0 = v.override ? 1 : v.g, L = REC.VOL_LIMIT_DB, Hd = REC.VOL_HEAD_DB;
        let g = g0, pk = 0, rounds = 0, clipped = false, gm = g0;
        for (; rounds < 2; ) {
          rounds++; gm = g; REC.volApply(g);
          ui.status('בדיקת עוצמה: השיר מתנגן 2 שניות…');
          seek(Math.max(0, span.t0 - 0.25)); play();
          const p0 = s.peaks.length; await new Promise((r) => setTimeout(r, 2250));
          pause(); E.pausedF = f00;
          pk = Math.max(0, ...s.peaks.slice(p0)); clipped = pk >= 0.98;
          if (pk < 1 / 32768) break;
          const pkDb = 20 * Math.log10(pk), cap = gm * Math.pow(10, (L - Hd - 0.5 - pkDb) / 20); // 0.5 dB margin
          if (v.override) break;
          const want = Math.max(REC.VOL_FLOOR, Math.min(v.by === 'clip' ? v.g : 1, cap));
          g = clipped ? Math.max(REC.VOL_FLOOR, Math.min(want, gm * 0.5)) : want; // clipped: the real level is unknown — at least −6 dB, then measure again
          if (!clipped || g >= gm - 1e-3) break;
        }
        // the pause completes later (fade, then suspend) and stores ITS position: wait for it, then back to the take's start
        for (let i = 0; i < 30 && E.ctx.state !== 'suspended'; i++) await new Promise((r) => setTimeout(r, 50));
        await new Promise((r) => setTimeout(r, 30)); E.pausedF = f00;
        const pkDb = pk > 0 ? 20 * Math.log10(pk) : -120, predDb = clipped && g >= gm - 1e-3 ? null : +(pkDb + 20 * Math.log10(g / gm)).toFixed(1);
        g = +g.toFixed(3); REC.volApply(g);
        bleed = { peakDb: +pkDb.toFixed(1), at: [+span.t0.toFixed(2), +span.t1.toFixed(2)], atSrc: span.src, measuredAt: +gm.toFixed(3), gainBefore: +g0.toFixed(3), gain: g, predictedDb: predDb, headroomDb: Hd, limitDb: L, rounds, clipped, override: !!v.override };
        if (!v.override) REC.volSet({ g, by: v.by === 'clip' && g >= v.g - 1e-3 ? 'clip' : 'check', override: false });
        REC.natChecked = Date.now(); REC.lastCheck = { peak: pk, native: true, bleed: true, gain: g };
        if (pk < 1 / 32768) { REC.volApply(1); await REC.natEnd(s); REC.busy = false; ui.recState(); REC.warn('המיקרופון לא קולט כלום. לבדוק את ההרשאה למיקרופון' + (REC.natChoice() ? ' או לנסות את המיקרופון השני' : '') + '.'); ui.status('ההקלטה לא התחילה'); REC.natChecked = 0; return 'done'; }
        if (predDb == null || predDb + Hd >= L) REC.warn('השיר חזק מדי למיקרופון גם בעוצמה ' + REC.pct(g) + (v.override ? ' (ההנמכה האוטומטית כבויה)' : '') + ': להנמיך את עוצמת הטלפון. קטעים שנחתכו לא ינוקו טוב.');
        else REC.warn(null);
      } else if (!REC.natChecked || Date.now() - REC.natChecked > 60000) { // 2 s level check (the recorder is already running)
        ui.status('בדיקת עוצמה: לשיר או לנגן משהו במשך 2 שניות…');
        const p0 = s.peaks.length; await new Promise((r) => setTimeout(r, 2000));
        const pk = Math.max(0, ...s.peaks.slice(p0)); REC.natChecked = Date.now(); REC.lastCheck = { peak: pk, native: true, bleed: false };
        if (pk < 1 / 32768) { await REC.natEnd(s); REC.busy = false; ui.recState(); REC.warn('המיקרופון לא קולט כלום. לבדוק את ההרשאה למיקרופון' + (REC.natChoice() ? ' או לנסות את המיקרופון השני' : '') + '.'); ui.status('ההקלטה לא התחילה'); REC.natChecked = 0; return 'done'; }
        if (pk >= 0.98) REC.warn('חזק מדי: הקלט מגיע לקצה (קליפינג). להרחיק את הטלפון מהפה או לשיר חלש יותר.');
        else if (pk < 0.03) { REC.low = true; REC.warn('הקלט חלש מאוד (שיא ' + REC.lr(REC.db(pk) + ' dB') + '). לשיר קרוב יותר לטלפון. ההקלטה תוגבר אוטומטית בהשמעה.'); } else REC.warn(null);
      }
      const ctx = E.ctx, f = E.pausedF >= E.durF - E.SR ? 0 : E.pausedF, cal = store.get(REC.latKey());
      REC.lastFallback = null; // Android's capture opened: any earlier fallback warning is over
      const ref = REC.mode === 'speaker' ? await REC.refTap() : null; // (v0.5.0) what the phone plays = the song to remove later
      const take = { id: s.id, songId: E.song.id, name: REC.nextName(), created: Date.now(), sr: E.SR, startF: f, endF: f, transpose: E.semi || 0, tempo: E.rate, engine: 'native', engineReason: 'native',
        latencyF: cal && Number.isFinite(cal.ms) ? Math.round(cal.ms * E.SR / 1000) : 0, calibrated: !!cal, calSrc: cal ? cal.src : null,
        route: REC.routeKey(), routeNative: REC.route(), mode: REC.mode, nudgeMs: 0, devices: REC.audioInfo(), bleed, gainSteps: bleed ? [] : undefined,
        mic: { label: s.info.preferred ? s.info.preferred.name + ' (' + s.info.preferred.type + ')' : 'ברירת מחדל', pref: REC.natChoice() ? REC.micPref() : null, ec: !!s.info.aec, ns: false, agc: false },
        ctxInfo: { sampleRate: E.SR, baseLatency: ctx.baseLatency, outputLatency: ctx.outputLatency },
        drops: { gaps: 0, gapFrames: 0, at: [], zeroRuns: 0, zeroFrames: 0, queueDropped: 0, writeRetries: 0, blocks: 0 } };
      const A = HV.A, bpm = (A && A.bpm) || 100, beats = (A && parseInt(A.meter, 10)) || 4, beat = 60 / bpm;
      const t0 = ctx.currentTime + 0.25, hi = REC.clickBuf(1500, 30, 0.6), lo = REC.clickBuf(1000, 30, 0.45), items = [];
      for (let i = 0; i < beats; i++) { const F = Math.round((t0 + i * beat) * E.SR), w = i ? lo : hi; REC.click(F / E.SR, w); items.push({ F, w: w.getChannelData(0) }); }
      REC.cur = { native: true, s, take, items, run: null, endCtxF: Infinity, ref };
      REC.on = true; REC.busy = false; document.body.classList.add('recording'); ui.recState();
      E.playing = true; ui.state();
      stopRun(E.run, 0); E.run = null; // (v0.4.7) the paused run's scheduled sources would play on under the new run: a doubled song
      startAt(f, t0 + beats * beat);
      REC.cur.run = E.run;
      ui.status('מקליט' + (REC.mode === 'speaker' ? ' (מצב רמקול)' : ' (מצב אוזניות)') + '… (⏺ או ⏸ לסיום)');
      return 'done';
    },
    async stopNative() {
      const R = REC.cur, t = R.take, SR = E.SR; REC.on = false; document.body.classList.remove('recording');
      R.endCtxF = Math.round(E.ctx.currentTime * SR); REC.cur = null; ui.recState();
      ui.status('שומר את ההקלטה…');
      const n = await REC.natEnd(R.s); t.native = n.diag;
      const refBlocks = R.ref ? R.ref.stop() : null;
      if (t.bleed) { t.gainEnd = +(REC.volNow || 1).toFixed(3); REC.volApply(1); } // playback afterwards at the normal level
      t.truncatedMs = n.diag.truncatedMs;
      const r = R.run;
      if (!n.ok || !r || r.T0F == null) { ui.status('ההקלטה לא נשמרה (' + (n.ok ? 'no run' : 'no data') + ')'); return; }
      // the take's own count-in (heard when the mic hears the phone): residual within ±150 ms
      const W = Math.round(0.15 * SR), last = R.items[R.items.length - 1].F;
      const kA = REC.natKFor(n, R.items[0].F) - W - 2048, kB = REC.natKFor(n, last) + 2 * W + 4096;
      const res = REC.measureLag(REC.natBlocks(n, kA, kB, W), R.items, 2 * W);
      t.countIn = { ms: +((res.lagF - W) * 1000 / SR).toFixed(2), snr: +res.snr.toFixed(1), agree: res.agree + '/' + res.n };
      let L = t.latencyF;
      const okCI = res.snr >= 6 && res.agree >= Math.max(3, res.n - 1) && !t.calibrated; t.countIn.used = okCI; // (headphones: never over a calibration)
      if (okCI) { L = res.lagF - W; t.latSource = 'count-in'; } else t.latSource = t.calibrated ? 'calibration' : 'estimate';
      t.latencyF = L;
      // write the song-frame grid (Int16 straight from the recording)
      const C = E.Lf, chunks = new Map(), st = REC.newStats(), dr = t.drops, Kr = Math.round(n.K);
      const SL = Math.round(REC.audLat(r)); t.shiftLatF = SL; // (v0.5.3) heard = rendered − the shifter's delay (0 at transpose 0)
      let z = 0, zFrom = 0, prevA = 0, lastF = -1, lastLost = 0;
      for (let k = 0; k < n.pcm.length; k++) {
        const lk = n.lost(k); if (lk !== lastLost) { dr.gaps++; dr.gapFrames += lk - lastLost; if (dr.at.length < 20) dr.at.push([Kr + k + lastLost - SL - r.T0F - L, lk - lastLost]); lastLost = lk; }
        const cf = Kr + k + lk; if (cf >= R.endCtxF) break;
        const f = cf - SL - r.T0F - L; if (f < t.startF || f >= E.durF) continue;
        const kk = Math.floor(f / C); let a = chunks.get(kk); if (!a) { a = new Int16Array(C); chunks.set(kk, a); }
        const s16 = n.pcm[k]; a[f - kk * C] = s16; const v = s16 / 32768; REC.acc(st, v); REC.clip(R, v);
        if (s16 === 0) { if (!z++) zFrom = prevA; } else { if (z >= 32 && zFrom > 0.002) { dr.zeroRuns++; dr.zeroFrames += z; } z = 0; prevA = v < 0 ? -v : v; }
        if (f > lastF) lastF = f;
      }
      if (lastF < 0 || lastF + 1 - t.startF < SR * 0.5) { ui.status('ההקלטה קצרה מדי — לא נשמרה'); return; }
      t.endF = lastF + 1;
      const lv = REC.levels(st);
      t.level = { peakDb: REC.db(lv.peak), rmsDb: REC.db(lv.rms), loudDb: REC.db(lv.loud), clips: R.clips || 0, clipSamples: R.clipS || 0 };
      t.gain = REC.autoGain(lv); t.norm = true; t.samples = st.n;
      try {
        for (const [k, a] of chunks) { let ok = false; for (let i = 0; i < 4 && !ok; i++) { try { await REC.putChunk(t.id, k, a); ok = true; } catch (e) { dr.writeRetries++; await new Promise((q) => setTimeout(q, 300 * (i + 1))); } } if (!ok) throw new Error('chunk'); }
        await REC.op('takes', 'readwrite', (x) => x.put(t));
      } catch (e) { ui.status('שמירת ההקלטה נכשלה'); return; }
      if (refBlocks && r && r.T0F != null) { // the played mix on the song timeline (song frame = context frame − T0F at 100 %)
        try { await REC.putRef(t, refBlocks, r.T0F + SL); t.hasRef = true; t.cleanOn = true; await REC.op('takes', 'readwrite', (x) => x.put(t)); } catch (e) { t.hasRef = false; }
      }
      REC.takes.push(t); REC.setActive(t, true); PK.afterTake(t);
      if (t.hasRef) REC.cleanTake(t);
      if (lv.loud < 0.01) REC.low = true;
      const notes = [];
      if (!t.calibrated && t.latSource !== 'count-in') notes.push('כדאי לעשות כיול לסנכרון מדויק');
      if (dr.gaps || dr.zeroRuns) notes.push('זוהו קטיעות בקלט (ראו "פרטים")');
      if (t.truncatedMs > 100) { notes.push('ההקלטה נקטעה לפני הסוף'); REC.warn('ההקלטה נקטעה לפני הסוף (חסרות ' + REC.lr((t.truncatedMs / 1000).toFixed(1) + ' s') + ' בסוף). ההקלטה נשמרה עד שם.'); }
      if (t.gainSteps && t.gainSteps.some((x) => x.by === 'clip')) notes.push('עוצמת השיר הונמכה במהלך ההקלטה ל-' + REC.pct(t.gainEnd || 1));
      if (t.level.clips) notes.push('חזק מדי: נחתך ' + t.level.clips + ' פעמים (קליפינג) — להרחיק את הטלפון או לשיר חלש יותר');
      if (t.gain >= 2) notes.push('הוגבר אוטומטית ב-' + REC.lr(Math.round(20 * Math.log10(t.gain)) + ' dB'));
      ui.status('נשמרה "' + t.name + '"' + (notes.length ? ' — ' + notes.join(' · ') : ''));
      ui.recState();
    },
    // calibration through the native recorder: clicks scheduled, recorded, then the same analysis on the context axis
    async calNative() {
      REC.busy = true; ui.recState();
      try {
        if (!(await REC.natPerm())) { ui.status('אין הרשאה למיקרופון'); return 'done'; }
        const s = REC.natBegin('c'); if (!s) return 'fallback';
        await new Promise((r) => setTimeout(r, 300)); // recorder warm-up
        const ctx = E.ctx, SR = E.SR; let F, until, kind;
        if (REC.mode === 'speaker') {
          ui.status('כיול: שקט בבקשה…'); kind = 'loopback';
          const offs = [0, 0.37, 0.81, 1.19, 1.66, 2.03, 2.47, 2.88], wave = REC.clickBuf(2000, 4, 0.9), t0 = ctx.currentTime + 0.4;
          F = offs.map((o) => Math.round((t0 + o) * SR)); F.forEach((fr) => REC.click(fr / SR, wave)); s.wave = wave.getChannelData(0);
          until = F[F.length - 1] / SR + 0.9;
        } else {
          ui.status('כיול במחיאות כפיים: 4 קליקים להתכונן, ואז למחוא כף אחת יחד עם כל אחד מ-8 הקליקים הגבוהים'); kind = 'clap';
          const lo = REC.clickBuf(1000, 30, 0.45), hi = REC.clickBuf(1500, 30, 0.6), t0 = ctx.currentTime + 1.5; F = [];
          for (let i = 0; i < 12; i++) { const fr = Math.round((t0 + i * 0.6) * SR); REC.click(fr / SR, i < 4 ? lo : hi); if (i >= 4) F.push(fr); }
          until = F[7] / SR + 0.65;
        }
        while (ctx.currentTime < until) await new Promise((r) => setTimeout(r, 50));
        const n = await REC.natEnd(s); REC.lastNat = n.diag;
        if (!n.ok) { ui.status('הכיול לא הצליח: לא התקבלה הקלטה'); return 'done'; }
        const W = Math.round(0.15 * SR), kA = REC.natKFor(n, F[0]) - W - 4096, kB = REC.natKFor(n, F[F.length - 1]) + Math.round(0.6 * SR) + 4096;
        if (kind === 'loopback') {
          const res = REC.measureLag(REC.natBlocks(n, kA, kB, W), F.map((fr) => ({ F: fr, w: s.wave })), 2 * W + Math.round(0.45 * SR));
          REC.lastCal = { ...res, ms: (res.lagF - W) * 1000 / SR, native: true };
          if (res.snr < 6 || res.agree < 5) { ui.status('הכיול לא הצליח: הקליקים לא נשמעו ברור במיקרופון. לנסות שוב בשקט'); return 'done'; }
          store.set(REC.latKey(), { ms: REC.lastCal.ms, at: Date.now(), src: 'loopback', engine: 'native' });
          ui.status('כיול: תיקון ' + REC.lr(Math.round(REC.lastCal.ms) + ' ms') + ' (מנוע אנדרואיד)');
        } else {
          const res = REC.clapAnalyze(REC.natBlocks(n, kA, kB), F, SR, true); REC.lastClap = res;
          if (!res.ok) { ui.status(res.why); return 'done'; }
          store.set(REC.latKey(), { ms: res.ms, at: Date.now(), src: 'clap', n: res.used, sd: +res.sd.toFixed(1), engine: 'native' });
          ui.status('כיול במחיאות: תיקון ' + REC.lr(Math.round(res.ms) + ' ms') + ' (' + res.used + ' מתוך 8 מחיאות, פיזור ' + REC.lr(Math.round(res.sd) + ' ms') + ')');
        }
        return 'done';
      } finally { REC.busy = false; REC.meterShow(false); ui.recState(); }
    },
    // ---- take-channel effects (v0.4.6): settings per take (t.fx), applied live to the channel's effect graph
    fxOf: (t) => ({ ...FX_DEF, ...((t && t.fx) || {}) }),
    fxApply() { const st = E.stems && E.stems.find((x) => x.fx); if (st) st.fx.set(REC.fxOf(REC.active)); REC.fxSync(); },
    fxSet(patch) {
      const t = REC.active; if (!t) return;
      t.fx = { ...REC.fxOf(t), ...patch }; REC.fxApply();
      clearTimeout(REC.fxT); REC.fxT = setTimeout(() => REC.op('takes', 'readwrite', (st) => st.put(t)).catch(() => {}), 300);
    },
    fxUi(row) { // on the "ההקלטה שלי" mixer row
      const wrap = el('div', 'ch-fx'), tog = el('button', 'chip', 'אפקטים'); tog.type = 'button'; tog.id = 'fxToggle';
      const box = el('div', 'fx-box'); box.id = 'fxBox'; box.hidden = true;
      const amount = (key, label, ariaName) => { // − value + (5 % per tap; held: repeats after 0.4 s every 120 ms)
        const r = el('div', 'fx-row'), lab = el('span', 'fx-lab', label), grp = el('div', 'fx-grp'); grp.dir = 'ltr';
        const minus = el('button', 'chip fx-b', '−'), val = el('span', 'fx-val'), plus = el('button', 'chip fx-b', '+');
        minus.type = plus.type = 'button'; minus.setAttribute('aria-label', ariaName + ' פחות'); plus.setAttribute('aria-label', ariaName + ' יותר');
        val.id = 'fxVal-' + key;
        [[minus, -5], [plus, 5]].forEach(([b, d]) => {
          let rep = 0, down = false;
          const step = () => { const v = REC.fxOf(REC.active); REC.fxSet({ [key]: clamp(v[key] + d, 0, 100) }); };
          const up = () => { down = false; clearTimeout(rep); clearInterval(rep); };
          b.addEventListener('pointerdown', (e) => { if (!REC.active || e.button > 0) return; down = true; step(); try { b.setPointerCapture(e.pointerId); } catch (x) { /* noop */ } rep = setTimeout(() => { rep = setInterval(step, 120); }, 400); });
          ['pointerup', 'pointercancel', 'lostpointercapture'].forEach((ev) => b.addEventListener(ev, up));
          b.addEventListener('keydown', (e) => { if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); step(); } });
          b.addEventListener('contextmenu', (e) => e.preventDefault());
        });
        grp.append(minus, val, plus); r.append(lab, grp); return r;
      };
      const clean = el('button', 'chip', 'ניקוי קול'); clean.type = 'button'; clean.id = 'fxClean';
      const reset = el('button', 'chip', 'איפוס'); reset.type = 'button'; reset.id = 'fxReset';
      const acts = el('div', 'fx-acts'); acts.append(clean, reset);
      box.append(amount('reverb', 'ריוורב (הדהוד)', 'ריוורב'), amount('echo', 'הד', 'הד'), acts);
      tog.addEventListener('click', () => { if (!REC.active) return; REC.fxSet({ on: !REC.fxOf(REC.active).on }); });
      clean.addEventListener('click', () => { if (!REC.active) return; REC.fxSet({ clean: !REC.fxOf(REC.active).clean }); });
      reset.addEventListener('click', () => { if (!REC.active) return; REC.fxSet({ reverb: FX_DEF.reverb, echo: FX_DEF.echo, clean: FX_DEF.clean }); });
      wrap.append(tog, box); row.append(wrap);
      REC.fxSync();
    },
    fxSync() {
      const tog = $('fxToggle'); if (!tog) return;
      const v = REC.fxOf(REC.active);
      tog.classList.toggle('on', v.on); tog.setAttribute('aria-pressed', String(v.on)); tog.setAttribute('aria-expanded', String(v.on));
      tog.textContent = 'אפקטים: ' + (v.on ? 'פועלים' : 'כבויים');
      $('fxBox').hidden = !v.on;
      $('fxVal-reverb').textContent = v.reverb + '%'; $('fxVal-echo').textContent = v.echo + '%';
      const c = $('fxClean'); c.classList.toggle('on', v.clean); c.setAttribute('aria-pressed', String(v.clean));
    },
    // ---- take details + export (v0.4.1)
    details(t) {
      const SR = t.sr || E.SR, ms = (f) => (Math.round(f * 10000 / SR) / 10) + ' ms';
      if (cpIsComp(t)) { // (v0.9.0) a comp: where each line came from
        const c = t.comp || {}, by = new Map(); (c.rows || []).forEach((x) => { if (x.take) by.set(x.take, (by.get(x.take) || 0) + 1); });
        const lv = t.level;
        return [
          ['מקור', 'הרכבה מ-' + (c.sources || []).length + ' הקלטות' + (c.of ? ' (עריכה של הרכבה קודמת)' : '')],
          ['שורות', (c.sources || []).map((x) => x.name + ': ' + (by.get(x.id) || 0) + (x.src === 'clean' ? ' (נקייה 🧹)' : '')).join(' · ') || '—'],
          ['מעברים', (c.cuts || []).length + ' · הצלבה ' + REC.lr((c.xfMs || 30) + ' ms') + ' · בהפסקה בין שורות: ' + (c.cuts || []).filter((x) => x.kind === 'gap').length + (c.mixed ? ' · נקייה ולא נקייה מעורבות' : '')],
          ['עוצמה', lv ? 'שיא ' + REC.lr(lv.peakDb + ' dB') + ' · RMS ' + REC.lr(lv.rmsDb + ' dB') : '—'],
          ['נרמול', t.norm === false ? 'כבוי' : REC.lr('+' + (20 * Math.log10(t.gain || 1)).toFixed(1) + ' dB') + ' (כמו בהקלטות המקוריות)'],
          ['אורך', fmt((t.endF - t.startF) / SR) + ' (' + fmt(t.startF / SR) + '–' + fmt(t.endF / SR) + ')'],
          ['סולם וקצב', 'סולם ' + REC.lr((t.transpose > 0 ? '+' : t.transpose < 0 ? '−' : '') + Math.abs(t.transpose || 0)) + ' · קצב ' + REC.lr(Math.round((t.tempo || 1) * 100) + '%')],
          ['נוצרה', new Date(t.created).toLocaleString('he-IL') + ' · ' + REC.lr(((c.ms || 0) / 1000).toFixed(1) + ' s')],
        ];
      }
      const src = { 'count-in': 'נמדדה בספירה', calibration: t.calSrc === 'clap' ? 'כיול במחיאות כפיים' : 'כיול קליקים', estimate: 'הערכה (בלי כיול)' }[t.latSource] || t.latSource || '—';
      const dr = t.drops, lv = t.level, mic = t.mic || {}, dev = t.devices;
      const rows = [
        ['מצב', t.mode === 'speaker' ? (t.engine === 'native' ? 'רמקול (הקלטה ישירה, השיר מוסר אחרי העצירה)' : 'רמקול (ביטול הד פעיל)') : 'אוזניות (בלי ביטול הד)'],
        ['יציאת שמע', (t.route || '—') + (t.routeNative && t.routeNative !== t.route ? ' (' + t.routeNative + ')' : '')],
        ['מיקרופון', (mic.label || '—') + (mic.pref ? ' · בחירה: ' + (mic.pref === 'headset' ? 'אוזניות' : 'טלפון') : '') + (mic.fallback ? ' · ברירת מחדל' : '')],
        ['עיבוד', 'ביטול הד ' + (mic.ec ? 'פעיל' : 'כבוי') + ' · דיכוי רעש ' + (mic.ns ? 'פעיל' : 'כבוי') + ' · הגברה אוטומטית ' + (mic.agc ? 'פעילה' : 'כבויה')],
        ['קצב דגימה', SR + ' Hz' + (t.settings && t.settings.sampleRate && t.settings.sampleRate !== SR ? ' (מיקרופון ' + t.settings.sampleRate + ')' : '')],
        [t.engine === 'native' ? 'תיקון סנכרון' : 'השהיה', REC.lr(ms(t.latencyF)) + ' · ' + src + (t.countIn ? ' · ספירה: ' + REC.lr(t.countIn.ms + ' ms, SNR ' + t.countIn.snr + ', ' + t.countIn.agree) + (t.countIn.used === false ? ' (לא בשימוש)' : '') : '')],
        ['עוצמה', lv ? 'שיא ' + REC.lr(lv.peakDb + ' dB') + ' · RMS ' + REC.lr(lv.rmsDb + ' dB') + ' · חלקים חזקים ' + REC.lr(lv.loudDb + ' dB') + (lv.clips != null ? ' · קליפינג: ' + lv.clips + (lv.clips ? ' (' + lv.clipSamples + ' דגימות)' : '') : '') : '—'],
        ['נרמול', t.gain ? (t.norm === false ? 'כבוי' : REC.lr('+' + (20 * Math.log10(t.gain)).toFixed(1) + ' dB')) : '—'],
        ['קטיעות', dr ? dr.gaps + ' פערים (' + dr.gapFrames + ' דגימות) · ' + dr.zeroRuns + ' שקטים פתאומיים · ' + dr.writeRetries + ' כתיבות חוזרות' + (dr.queueDropped ? ' · ' + dr.queueDropped + ' בלוקים אבדו' : '') +
          (dr.stampSlips != null ? ' · חותמות זמן: ' + dr.stampSlips + ' תוקנו, ' + dr.resyncs + ' סנכרונים מחדש' + (dr.inputMissing ? ', ' + dr.inputMissing + ' בלי קלט' : '') + (dr.offMax != null ? ', סטייה מרבית ' + dr.offMax : '') : '') : '—'],
        ['אורך', fmt((t.endF - t.startF) / SR) + ' (' + fmt(t.startF / SR) + '–' + fmt(t.endF / SR) + ')'],
        ['סולם וקצב', t.transpose != null ? 'סולם ' + REC.lr((t.transpose > 0 ? '+' : t.transpose < 0 ? '−' : '') + Math.abs(t.transpose)) + ' · קצב ' + REC.lr(Math.round((t.tempo || 1) * 100) + '%') + (t.shiftLatF ? ' · השהיית שינוי הסולם ' + REC.lr(t.shiftLatF + ' דגימות') : '') : 'סולם מקורי (גרסה ישנה)'], // (v0.5.3)
      ];
      rows.splice(1, 0, ['מנוע', t.engine === 'native' ? 'אנדרואיד (' + ((t.native && t.native.source) || '?') + ')' : 'דפדפן (getUserMedia)' + (t.engineReason ? ' — ' + REC.reasonHe(t.engineReason) : ' — סיבה לא נשמרה (גרסה ישנה)')]);
      if (t.clean) { const c = t.clean; rows.push(['ניקוי השיר', c.error ? 'נכשל: ' + c.error : (t.cleanOn !== false ? 'פועל (🧹)' : 'כבוי — מושמע המקור') + ' · הנחת השיר ' + REC.lr((c.reductionDb != null ? c.reductionDb : '?') + ' dB')
        + ' · יישור ' + REC.lr(c.alignMs + ' ms') + ' · התכנסות (dB לאורך ההקלטה) ' + REC.lr((c.linearErleDb || []).filter((x) => x != null).join(' / ')) + ' · שיר בלבד ' + c.songOnlySec + ' ש׳, שירה ' + c.singingSec + ' ש׳ · ' + REC.lr(Math.round((c.wallMs || c.ms) / 100) / 10 + ' s')]); }
      else if (t.hasRef) rows.push(['ניקוי השיר', REC.cleaning === t.id ? 'מנקה…' : 'ממתין']);
      if (t.clean && !t.clean.error && t.clean.v >= 2) rows.push(['ניקוי (פרטים)', 'גרסה ' + t.clean.v + ' · השיר כ' + (t.clean.refSrc === 'stereo' ? 'סטריאו (שני הרמקולים)' : t.clean.refSrc === 'stems' ? 'סטריאו משוחזר מהערוצים (התאמה ' + REC.lr(t.clean.fitDb + ' dB') + ')' : 'מונו' + (t.clean.fitDb != null ? ' (שחזור לא התאים: ' + REC.lr(t.clean.fitDb + ' dB') + ')' : '')) + ' · מסנן חדר ' + REC.lr(t.clean.roomFilterPct + '%') + ', מעקב ' + REC.lr(t.clean.trackingPct + '%') + ' · מוגן ' + t.clean.guardedSec + ' ש׳ · קליפינג ' + t.clean.clippedSec + ' ש׳']);
      if (t.bleed) { const b = t.bleed, st = (t.gainSteps || []).filter((x) => x.by === 'clip');
        rows.push(['עוצמת השיר', (b.gain < 0.995 ? 'עוצמת השיר הונמכה ל-' + REC.pct(b.gain) : 'עוצמה מלאה (100%)') + (b.override ? ' · בלי הנמכה אוטומטית' : '')
          + ' · בדיקה: שיא ' + REC.lr(b.peakDb + ' dB') + (b.clipped ? ' (נחתך)' : '') + ' ב-' + fmt(b.at[0]) + '–' + fmt(b.at[1]) + (b.atSrc === 'loudest' ? ' (הקטע החזק בשיר)' : '') + ' בעוצמה ' + REC.pct(b.measuredAt)
          + (b.predictedDb != null ? ' · צפוי ' + REC.lr(b.predictedDb + ' dB') : '') + (st.length ? ' · הונמכה במהלך ההקלטה ' + st.length + ' פעמים, עד ' + REC.pct(t.gainEnd || st[st.length - 1].to) : '')]); }
      if (t.truncatedMs != null) rows.push(['קטיעה בסוף', t.truncatedMs > 100 ? 'ההקלטה נקטעה לפני הסוף: ' + REC.lr(t.truncatedMs + ' ms') : 'לא (' + REC.lr(t.truncatedMs + ' ms') + ')']);
      { const v = REC.fxOf(t); rows.push(['אפקטים', v.on ? 'פועלים · ריוורב ' + v.reverb + '% · הד ' + v.echo + '% · ניקוי קול ' + (v.clean ? 'פעיל' : 'כבוי') + ' (בהשמעה בלבד)' : 'כבויים']); }
      if (t.native) rows.push(['אנדרואיד', JSON.stringify(t.native)]);
      if (t.settings) rows.push(['getSettings', JSON.stringify(t.settings)]);
      if (dev) rows.push(['התקנים', JSON.stringify({ outs: dev.outs, ins: dev.ins, sdk: dev.sdk })]);
      return rows;
    },
    async exportFiles(t) {
      const n = t.endF - t.startF, pcm = new Int16Array(n), C = E.Lf;
      for (let k = Math.floor(t.startF / C); k * C < t.endF; k++) {
        const d = await REC.getChunk(t.id, k); if (!d) continue;
        const base = k * C; for (let f = Math.max(t.startF, base); f < Math.min(t.endF, base + C); f++) pcm[f - t.startF] = d[f - base];
      }
      const wav = new Uint8Array(44 + n * 2), v = new DataView(wav.buffer), str = (o, s) => { for (let i = 0; i < s.length; i++) v.setUint8(o + i, s.charCodeAt(i)); };
      str(0, 'RIFF'); v.setUint32(4, 36 + n * 2, true); str(8, 'WAVE'); str(12, 'fmt '); v.setUint32(16, 16, true); v.setUint16(20, 1, true); v.setUint16(22, 1, true);
      v.setUint32(24, t.sr, true); v.setUint32(28, t.sr * 2, true); v.setUint16(32, 2, true); v.setUint16(34, 16, true); str(36, 'data'); v.setUint32(40, n * 2, true);
      new Int16Array(wav.buffer, 44, n).set(pcm);
      const meta = { app: 'harmony', version: ($('ver') && $('ver').textContent) || '', userAgent: navigator.userAgent, song: E.song.id, take: { ...t, pitch: undefined },
        details: Object.fromEntries(REC.details(t)), fx: REC.fxOf(t), note: 'wav = the raw take (before the playback gain and the playback effects); -clean.wav (speaker takes) = the same with the played song removed; take.startF = its first song frame' };
      let cwav = null; // (v0.5.0) the cleaned track as a second WAV (the raw one stays the original)
      if (t.clean && !t.clean.error) { const c = await REC.trackOf(t.id + ':c', t); cwav = new Uint8Array(wav.length); cwav.set(wav.subarray(0, 44)); const ci = new Int16Array(cwav.buffer, 44, n); for (let i = 0; i < n; i++) { const q = c[i]; ci[i] = q >= 1 ? 32767 : q <= -1 ? -32768 : Math.round(q * 32767); } }
      return { wav, cwav, json: new TextEncoder().encode(JSON.stringify(meta, null, 2)), base: 'harmony-' + E.song.id + '-' + t.id };
    },
    async share(t) {
      ui.status('מכין את הקבצים לשליחה…');
      try {
        const f = await REC.exportFiles(t), A = window.Android;
        if (ANDROID && A.shareBegin) { // native share sheet: files written into the app's cache in base64 pieces
          const b64 = (u) => { let s = ''; for (let i = 0; i < u.length; i += 32768) s += String.fromCharCode.apply(null, u.subarray(i, i + 32768)); return btoa(s); };
          const put = async (name, u) => { for (let i = 0; i < u.length; i += 393216) { if (!A.shareChunk(name, b64(u.subarray(i, i + 393216)))) throw new Error('chunk'); await new Promise((r) => setTimeout(r, 0)); } };
          if (!A.shareBegin()) throw new Error('begin');
          await put(f.base + '.wav', f.wav); await put(f.base + '.json', f.json); if (f.cwav) await put(f.base + '-clean.wav', f.cwav);
          if (!A.shareEnd(f.base + '.wav,' + f.base + '.json' + (f.cwav ? ',' + f.base + '-clean.wav' : ''), f.base + '.zip')) throw new Error('end'); // one .zip, no EXTRA_TEXT
        } else { // a browser: two downloads
          [[f.wav, '.wav', 'audio/wav'], [f.json, '.json', 'application/json'], ...(f.cwav ? [[f.cwav, '-clean.wav', 'audio/wav']] : [])].forEach(([u, ext, type]) => {
            const a = document.createElement('a'); a.href = URL.createObjectURL(new Blob([u], { type })); a.download = f.base + ext;
            document.body.append(a); a.click(); a.remove(); setTimeout(() => URL.revokeObjectURL(a.href), 10000);
          });
        }
        REC.lastExport = { base: f.base, wavBytes: f.wav.length, jsonBytes: f.json.length };
        ui.status('');
      } catch (e) { ui.status('השליחה נכשלה'); }
    },
    list() {
      const box = $('takeList'), sec = $('takes');
      sec.hidden = !REC.takes.length;
      if ($('cpOpen')) $('cpOpen').hidden = REC.takes.filter((x) => !cpIsComp(x)).length < 2; // (v0.9.0)
      const prim = store.get(REC.primaryKey());
      box.replaceChildren(...REC.takes.slice().reverse().map((t) => {
        const row = el('div', 'take' + (REC.active === t ? ' cur' : ''));
        row.dataset.id = t.id;
        const info = el('div', 'take-info');
        const tm = el('span', 'take-meta'); tm.append(bdi(fmt(t.startF / E.SR) + '–' + fmt(t.endF / E.SR))); if (t.id === prim) tm.append(document.createTextNode(' · ראשית'));
        info.append(el('span', 'take-name', t.name), tm);
        if (t.mode === 'speaker' && !cpIsComp(t)) { const bg = el('span', 'badge warn', '🔈 רמקול'); bg.title = t.engine === 'native' ? 'הוקלט במצב רמקול: השיר מוסר מההקלטה אחרי העצירה (🧹)' : 'הוקלט במצב רמקול: ביטול ההד עלול להחליש את הקול כשהשיר חזק'; info.append(bg); }
        if (t.drops && (t.drops.gaps || t.drops.zeroRuns || t.drops.queueDropped)) info.append(el('span', 'badge warn', 'קטיעות'));
        if (t.level && t.level.clips) info.append(el('span', 'badge warn', 'חזק מדי'));
        const pb = el('button', 'chip', '▶ השמעה'); pb.type = 'button';
        pb.addEventListener('click', () => { if (REC.active !== t) REC.setActive(t, false); seek(t.startF / E.SR); if (!E.playing) play(); });
        const pr = el('button', 'chip' + (t.id === prim ? ' on' : ''), 'ראשית'); pr.type = 'button'; pr.setAttribute('aria-pressed', String(t.id === prim));
        pr.addEventListener('click', () => REC.setActive(t, true));
        const det = el('button', 'chip', 'פרטים'); det.type = 'button'; det.setAttribute('aria-expanded', 'false');
        const sh = el('button', 'chip', 'שלח לי'); sh.type = 'button'; sh.addEventListener('click', () => REC.share(t));
        const del = el('button', 'chip', 'מחיקה'); del.type = 'button';
        del.addEventListener('click', () => {
          if (del.dataset.armed) { REC.remove(t); return; }
          del.dataset.armed = '1'; del.textContent = 'למחוק? שוב'; setTimeout(() => { delete del.dataset.armed; del.textContent = 'מחיקה'; }, 4000);
        });
        const va = el('button', 'chip', '🎙️ ניתוח'); va.type = 'button'; // (v0.7.0) this take's voice analysis
        va.addEventListener('click', () => { if (REC.active !== t) REC.setActive(t, false); vaOpen('take'); });
        const acts = el('div', 'take-acts'); acts.append(pb, pr, va, det, sh, del);
        if (cpIsComp(t)) { // (v0.9.0) a comp: its choices back in the comp screen (the result is a new comp)
          info.append(el('span', 'badge', '🎤 הרכבה'));
          const ed = el('button', 'chip', '✏️ עריכת ההרכבה'); ed.type = 'button';
          ed.addEventListener('click', () => { if (REC.active !== t) REC.setActive(t, false); cpOpen(); });
          acts.append(ed);
        }
        if (t.clean && !t.clean.error) { // (v0.5.0) 🧹: play the cleaned track (the song removed) or the raw take
          const on = t.cleanOn !== false, lab = 'ניקוי השיר מההקלטה: ' + (on ? 'פועל' : 'כבוי (מקורי)');
          const cb = el('button', 'skip as-btn' + (on ? ' on' : ''), null); cb.type = 'button'; cb.append(el('span', null, '🧹')); cb.firstChild.setAttribute('aria-hidden', 'true');
          cb.setAttribute('aria-pressed', String(on)); cb.setAttribute('aria-label', lab); cb.title = lab;
          cb.addEventListener('click', () => { t.cleanOn = !on; REC.op('takes', 'readwrite', (x) => x.put(t)).catch(() => {}); if (REC.active === t) REC.setActive(t, false); else REC.list(); });
          acts.append(cb);
        } else if (t.hasRef && REC.cleaning === t.id) acts.append(el('span', 'badge', 'מנקה…'));
        const box2 = el('div', 'take-det'); box2.hidden = true;
        const fillDet = () => {
          const dl = el('dl');
          REC.details(t).forEach(([k, v]) => { const dd = el('dd'); if (/^[\x20-\x7e]*$/.test(v)) dd.append(bdi(v)); else dd.textContent = v; dl.append(el('dt', null, k), dd); });
          const nb = el('button', 'chip' + (t.norm !== false ? ' on' : ''), 'נרמול אוטומטי'); nb.type = 'button'; nb.setAttribute('aria-pressed', String(t.norm !== false));
          nb.addEventListener('click', () => { t.norm = t.norm === false; REC.op('takes', 'readwrite', (st) => st.put(t)).catch(() => {}); if (REC.active === t) REC.setActive(t, false); else REC.list(); });
          const acts2 = el('div', 'take-acts'); acts2.append(nb);
          // (v0.4.9) no manual engine switch any more: Android's own capture always, WebView only in speaker mode or as the
          // automatic fallback when the native start fails (with a persistent warning and a retry)
          if (REC.nativeOk()) { // native source: VOICE_RECOGNITION (default, proven on the phone) or UNPROCESSED (opt-in, where the phone has it)
            const raw = REC.rawPref();
            const sb = el('button', 'chip' + (raw ? ' on' : ''), 'מקור: ללא עיבוד'); sb.type = 'button'; sb.setAttribute('aria-pressed', String(raw));
            sb.addEventListener('click', () => { if (REC.on || REC.busy) return; store.set('harmony.raw.v1', !REC.rawPref()); fillDet(); });
            acts2.append(sb);
          }
          box2.replaceChildren(dl, acts2);
        };
        det.addEventListener('click', () => { box2.hidden = !box2.hidden; det.setAttribute('aria-expanded', String(!box2.hidden)); if (!box2.hidden) fillDet(); });
        if (REC.openDet === t.id) { box2.hidden = false; det.setAttribute('aria-expanded', 'true'); fillDet(); }
        det.addEventListener('click', () => { REC.openDet = box2.hidden ? null : t.id; });
        row.append(info, acts, box2);
        return row;
      }));
      const t = REC.active, nb = $('nudgeBox');
      nb.hidden = !t;
      if (t) { const v = t.nudgeMs || 0; REC.nudgeV = v; $('nudgeVal').textContent = (v > 0 ? '+' : '') + v + ' ms'; $('nudgeName').textContent = t.name; }
    },
  };

  // ---------------------------------------------------------------- song library (v0.2.3; v0.6.0 imported songs)
  // songs/index.json lists the installed songs. v0.6.0: on the phone they are imported song packs (<id>.hsong, made by
  // tools/make-pack.sh) that the Android side unpacks into its own storage and serves at the same songs/<id>/ URLs; the
  // index is rewritten there on every import / delete. Every per-song state (takes, mix + tempo / key / loop, lyrics +
  // line fixes, latency) is keyed by the song id in the page's storage, so deleting a song (its audio only) and importing
  // it again brings all of it back. Switching = load the page for that song (location.replace): the old AudioContext,
  // its sources and every decoded chunk go away with the page — no overlap, no doubled memory.
  const PACKS = ANDROID && typeof window.Android.importPick === 'function' && typeof window.Android.importStatus === 'function';
  const LIB = { durs: {} };

  // ---------------------------------------------------------------- the song folder + the song's pack (v0.6.0)
  // Songs live in a folder the user picks once (Documents/Harmony by default), one "<id>.hsong" per song: the song's
  // files (as sent, never changed here) + the user's part: user.json (lyrics, mix, tempo, key, loop, active take, device
  // calibration) and takes/<take>/… (take.json + every audio chunk: raw, cleaned, speaker reference). The pack is the
  // source of truth; IndexedDB / localStorage are the working copy. Every change is marked (persisted, so a kill can't
  // lose the mark) and saved ~2 s later as ONE append transaction (Android: stage the files, packCommit -> new entries +
  // a new central directory after the old end, fsync, read back). A take's chunks are written once; after the save is
  // checked, the working copy of those chunks goes and they are read from the pack. Opening a song reconciles: a pack's
  // settings / takes the phone doesn't have come in (a reinstall), the phone's the pack doesn't have go out (vc27 data).
  const PACK_WARN_BYTES = 500 * 2 ** 20;    // a song's pack above this: suggest older takes to delete
  const FREE_WARN_BYTES = 2 * 2 ** 30;      // the phone's free space below this: a warning (start, after a take, before import)
  const FREE_REC_MIN_BYTES = 500 * 2 ** 20; // below this no new recording starts (a take is never cut mid-way)
  const SAVE_MARGIN_BYTES = 32 * 2 ** 20;   // kept free beyond any save into a pack (the Android side checks it too)
  const LIBS = PACKS && typeof window.Android.libState === 'function';
  const PKS = LIBS && typeof window.Android.packCommit === 'function';
  const fmtMB = (b) => '\u2066' + (b >= 2 ** 30 ? (b / 2 ** 30).toFixed(1) + ' GB' : Math.max(0, Math.round(b / 2 ** 20)) + ' MB') + '\u2069'; // (LTR isolate: "35 MB" in a Hebrew line)
  const freeBytes = () => { try { return LIBS ? Number(window.Android.freeBytes()) : -1; } catch (e) { return -1; } };
  const getJson = async (u) => { try { const r = await fetch(u, { cache: 'no-store' }); return r.ok ? await r.json() : null; } catch (e) { return null; } };
  const utf8 = (s) => new TextEncoder().encode(s);
  const b64 = (u8) => { let s = ''; for (let i = 0; i < u8.length; i += 0x8000) s += String.fromCharCode.apply(null, u8.subarray(i, i + 0x8000)); return btoa(s); };

  // ---- the folder: a folder that can't be reached says so (and blocks: the songs there are not lost) ----
  // (v0.10.1) first start no longer asks first: the songs are kept in the app (what "לא עכשיו" did) and the question
  // stays offered ("📁 איפה לשמור", the welcome card / the header) until a folder is picked or "לא עכשיו" is tapped.
  // LIB_ASK: 1 = still to ask, 0 = answered. Unset with the app's storage already chosen: a fresh page (nothing of the
  // app's in localStorage: the native side chose it, e.g. for a bundled song) asks; an older install had answered.
  const LIB_ASK = 'harmony.libask.v1';
  function libGate() {
    if (!LIBS) return true;
    let st = null; try { st = JSON.parse(window.Android.libState()); } catch (e) { return true; }
    let fresh = !st.mode; try { fresh = fresh || !Object.keys(localStorage).some((k) => k.startsWith('harmony.')); } catch (e) { /* noop */ }
    if (!st.mode) { try { window.Android.libDecline(); st = JSON.parse(window.Android.libState()); } catch (e) { /* noop */ } }
    if (st.mode === 'private' && store.get(LIB_ASK) == null) store.set(LIB_ASK, fresh ? 1 : 0);
    E.lib = st;
    setupWire(); libAskSync();
    if (st.mode === 'folder' && !st.ok) { setupShow('lost', st.label); return false; }
    return true;
  }
  function setupWire() {
    if (setupWire.done) return;
    setupWire.done = true;
    $('setupPick').addEventListener('click', libPick);
    $('setupNo').addEventListener('click', () => { store.set(LIB_ASK, 0); $('setup').hidden = true; libAskSync(); }); // already kept in the app: just the answer
    document.querySelectorAll('.lib-ask').forEach((b) => b.addEventListener('click', setupOffer));
  }
  function libAskSync() {
    const on = !!E.lib && E.lib.mode === 'private' && !!store.get(LIB_ASK);
    document.querySelectorAll('.lib-ask').forEach((b) => { b.hidden = !on; });
  }
  function setupShow(kind, label) { // the folder can't be reached
    document.body.classList.add('no-songs', 'setup-on'); E.empty = true;
    $('title').hidden = true; $('setup').hidden = false; ui.status('');
    $('setupLost').hidden = kind !== 'lost'; $('setupFirst').hidden = kind === 'lost'; $('setupNo').hidden = kind === 'lost';
    if (label) $('setupLabel').textContent = label;
  }
  function setupOffer() { // the folder question, when the user asks for it (opens / closes; never blocks)
    const box = $('setup'); box.hidden = !box.hidden;
    $('setupLost').hidden = true; $('setupFirst').hidden = false; $('setupNo').hidden = false; $('setupMsg').textContent = '';
    if (!box.hidden) box.scrollIntoView({ block: 'nearest', behavior: 'smooth' });
  }
  function libPick() {
    let seq0 = 0; try { seq0 = JSON.parse(window.Android.libOp()).seq; } catch (e) { /* noop */ }
    $('setupMsg').textContent = ''; window.Android.libPick();
    const poll = () => { let s = null; try { s = JSON.parse(window.Android.libOp()); } catch (e) { /* noop */ }
      if (!s || s.seq === seq0 || s.state === 'running') { setTimeout(poll, 300); return; }
      if (s.state === 'done') { try { sessionStorage.setItem('harmony.flash', 'השירים יישמרו בתיקייה ' + s.label + (s.moved ? (s.moved === 1 ? ' (שיר אחד הועבר אליה)' : ' (' + s.moved + ' שירים הועברו אליה)') : '')); } catch (e) { /* noop */ } location.replace(location.pathname); return; }
      if (s.state === 'error') { $('setupMsg').textContent = s.msg; impShow(s.msg, 'err'); } };
    setTimeout(poll, 300);
  }

  // ---- free space ----
  function spaceCheck(when) {
    const f = freeBytes(); if (f < 0) return f;
    const box = $('spaceBox');
    if (f < FREE_WARN_BYTES) {
      box.hidden = false;
      $('spaceTxt').textContent = 'נשארו רק ' + fmtMB(f) + ' פנויים בטלפון. כדאי לפנות מקום (תמונות, סרטונים, אפליקציות שלא צריך)' + (f < FREE_REC_MIN_BYTES ? ': עכשיו אין מספיק מקום להקלטה חדשה.' : ': כשהמקום נגמר אי אפשר להקליט או לשמור.');
    } else box.hidden = true;
    E.spaceLog = (E.spaceLog || []).concat([[when, f]]).slice(-20);
    return f;
  }
  function recRoomOk() { // before a recording: never start one that could be cut mid-way
    if (!LIBS) return true;
    const f = spaceCheck('rec');
    if (f >= 0 && f < FREE_REC_MIN_BYTES) { ui.status('אין מספיק מקום פנוי להקלטה: נשארו ' + fmtMB(f) + ', וצריך לפחות ' + fmtMB(FREE_REC_MIN_BYTES) + ' כדי שההקלטה לא תיקטע באמצע. אפשר לפנות מקום ולנסות שוב.'); return false; }
    return true;
  }

  // ---- the pack of the open song: marks, saves, reconcile ----
  const SONG_KEY = /^harmony\.(mix|loop|lyrics|lyrics\.auto|take)\.v1\.(.+)$/; // (v0.14.0) + lyrics.auto (found by name)
  const GLOBAL_KEY = /^harmony\.(lat\.v1\.|recmode\.v1\.|spkvol\.v1\.|micpref\.v1|autoscroll\.v1|pitchview\.v1|loopcount\.v1|agc\.v1|raw\.v1|takeN\.v1|practice\.v1|prcfg\.v1|vrange\.v1)/;
  const PK = {
    idx: null, busy: null, again: false, t: 0, last: 0, log: [], err: null, cache: new Map(),
    stamp() { PK.last = Math.max(Date.now(), PK.last + 1); return PK.last; },
    dirty() { try { return JSON.parse(localStorage.getItem('harmony.pk.dirty.v1')) || {}; } catch (e) { return {}; } },
    setDirty(d) { try { localStorage.setItem('harmony.pk.dirty.v1', JSON.stringify(d)); } catch (e) { /* noop */ } },
    // what changed: {user: true} | {take, json: true} | {take, key} | {take, voice: true} (v0.7.0: its analysis.json)
    mark(songId, w) {
      if (!PKS || !songId) return;
      const d = PK.dirty(), s = d[songId] || (d[songId] = { user: 0, takes: {} }), n = PK.stamp();
      if (w.user) s.user = n;
      if (w.take) { const t = s.takes[w.take] || (s.takes[w.take] = { json: 0, keys: {} }); if (w.json) t.json = n; if (w.key) t.keys[w.key] = n; if (w.voice) t.voice = n; }
      PK.setDirty(d); PK.schedule();
    },
    schedule(ms) { if (!PKS) return; clearTimeout(PK.t); PK.t = setTimeout(() => PK.flush(), ms == null ? 2000 : ms); },
    flush() { // one save at a time; a mark meanwhile -> another round
      if (!PKS) return Promise.resolve();
      if (PK.busy) { PK.again = true; return PK.busy; }
      // (the body starts on a microtask: a round with nothing to do must not finish before PK.busy is assigned)
      PK.busy = Promise.resolve().then(async () => {
        try { if (REC.on || REC.busy) { PK.schedule(3000); return; } // never write to the pack while recording
          const d = PK.dirty(), have = new Set(((E.index && E.index.songs) || []).map((s) => s.id));
          for (const id of Object.keys(d)) if (have.has(id)) { PK.step = 'save ' + id; await PK.save(id, d[id]); } // no pack yet: waits for the import
          PK.step = 'idle';
          await PK.compactIdle();
        } catch (e) { PK.err = String(e); }
        finally { PK.busy = null; if (PK.again) { PK.again = false; PK.schedule(400); } }
      });
      return PK.busy;
    },
    fileOf(key) { const p = key.split(':'); return (p.length === 2 ? 'a-' + p[1] : p[1] + '-' + p[2]) + '.i16'; }, // "<take>:<k>" / "<take>:c:<k>"
    async save(songId, snap) {
      const txn = 't' + Date.now().toString(36) + Math.random().toString(36).slice(2, 7), A = window.Android;
      if (!A.stageBegin(txn)) return;
      const puts = [], done = []; let bytes = 0, user = null;
      const stage = (file, u8) => { if (!u8.length) { if (!A.stageChunk(txn, file, '', false)) throw new Error('stage'); }
        for (let i = 0; i < u8.length; i += 393216) if (!A.stageChunk(txn, file, b64(u8.subarray(i, i + 393216)), i > 0)) throw new Error('stage');
        bytes += u8.length; };
      if (snap.user) { user = PK.userDoc(songId); stage('user.json', utf8(JSON.stringify(user))); puts.push({ name: 'user.json', file: 'user.json' }); }
      for (const tid of Object.keys(snap.takes || {})) {
        const t = snap.takes[tid], rec = await REC.op('takes', 'readonly', (st) => st.get(tid));
        // deleted meanwhile (that went to the pack as a delete); (v0.7.0) an analysis alone may belong to a take that is only in the pack
        if (!rec && !(t.voice && !t.json && !Object.keys(t.keys || {}).length)) continue;
        if (t.json && rec) { stage(tid + '.json', utf8(JSON.stringify(rec, (k, v) => (k === 'pitch' ? undefined : v)))); puts.push({ name: 'takes/' + tid + '/take.json', file: tid + '.json' }); } // (v0.7.0) the pitch cache is derived: not in the pack
        if (t.voice) { const a = await REC.op('tchunks', 'readonly', (st) => st.get(vaIdb(tid))); if (a) { stage(tid + '_analysis.json', utf8(JSON.stringify(a))); puts.push({ name: 'takes/' + tid + '/analysis.json', file: tid + '_analysis.json' }); } }
        for (const key of Object.keys(t.keys || {})) {
          const v = await REC.op('tchunks', 'readonly', (st) => st.get(key)); if (!v) continue;
          const f = PK.fileOf(key); stage(tid + '_' + f, new Uint8Array(v.buffer, v.byteOffset, v.byteLength));
          puts.push({ name: 'takes/' + tid + '/' + f, file: tid + '_' + f }); done.push(key);
        }
      }
      if (!puts.length) { PK.clear(songId, snap); return; }
      PK.step = 'stage ' + songId;
      const f = freeBytes();
      if (f >= 0 && f < bytes + SAVE_MARGIN_BYTES) { PK.err = 'space'; spaceCheck('save'); ui.status('אין מספיק מקום פנוי כדי לשמור לתיקיית השירים. השינויים שמורים באפליקציה ויישמרו בתיקייה כשיתפנה מקום.'); return; }
      PK.step = 'commit ' + songId;
      const r = await PK.job(A.packCommit(songId, txn, JSON.stringify({ puts, dels: [] })));
      PK.step = 'after ' + songId;
      PK.log.push({ songId, at: Date.now(), puts: puts.length, staged: bytes, takes: Object.keys(snap.takes || {}).length, ...r }); if (PK.log.length > 50) PK.log.shift();
      if (r.state !== 'done') { PK.err = r.code || 'error'; if (r.code === 'space') spaceCheck('save'); if (r.code === 'busy') PK.schedule(3000); else ui.status(r.msg || 'השמירה לתיקיית השירים נכשלה. השינויים שמורים באפליקציה.'); return; } // (v0.7.0) busy: the pack was just written by a killed app — try again shortly
      PK.err = null;
      if (r.compactSuggested) PK.want.add(songId); // many dead bytes: rewritten later, when nothing plays or records
      if (user) store.set('harmony.pk.userAt.' + songId, user.savedAt);
      PK.clear(songId, snap);
      // (v0.7.0) the phone keeps its copy of the saved chunks until a LATER start reads the pack back and finds them there
      // (PK.reconcile): a verified save once vanished when the app was killed seconds later; never the only copy before that
      PK.kept = (PK.kept || 0) + done.length;
      PK.step = 'reindex ' + songId;
      if (E.song && songId === E.song.id) PK.idx = await getJson('songs/' + songId + '/_pack.json') || PK.idx;
    },
    job(j) { return new Promise((res) => { if (!j) { res({ state: 'error', msg: 'השמירה לא התחילה.' }); return; }
      const poll = () => { let s = null; try { s = JSON.parse(window.Android.packJob(j)); } catch (e) { /* noop */ } if (!s || s.state === 'running') setTimeout(poll, 150); else res(s); }; poll(); }); },
    isDirty(songId, key) { const s = PK.dirty()[songId], tid = key.split(':')[0]; return !!(s && s.takes[tid] && s.takes[tid].keys[key]); },
    clear(songId, snap) { // marks saved now go; a newer mark (changed again meanwhile) stays
      const d = PK.dirty(), s = d[songId]; if (!s) return;
      if (snap.user && s.user === snap.user) s.user = 0;
      for (const tid of Object.keys(snap.takes || {})) { const a = s.takes[tid], b = snap.takes[tid]; if (!a) continue;
        if (b.json && a.json === b.json) a.json = 0;
        if (b.voice && a.voice === b.voice) a.voice = 0;
        for (const k of Object.keys(b.keys || {})) if (a.keys[k] === b.keys[k]) delete a.keys[k];
        if (!a.json && !a.voice && !Object.keys(a.keys).length) delete s.takes[tid]; }
      if (!s.user && !Object.keys(s.takes).length) delete d[songId];
      PK.setDirty(d);
    },
    userDoc(id) { // the song's settings + the device's (calibration, record mode, …: restored only where the phone has none)
      const raw = (k) => { const v = localStorage.getItem(k); try { return v == null ? null : JSON.parse(v); } catch (e) { return null; } };
      const g = {}; for (let i = 0; i < localStorage.length; i++) { const k = localStorage.key(i); if (GLOBAL_KEY.test(k)) g[k] = raw(k); }
      return { v: 1, songId: id, savedAt: PK.stamp(), app: '0.14.0', song: { mix: raw('harmony.mix.v1.' + id), loop: raw('harmony.loop.v1.' + id), lyrics: raw('harmony.lyrics.v1.' + id), lyricsAuto: raw('harmony.lyrics.auto.v1.' + id), take: raw('harmony.take.v1.' + id) }, global: g };
    },
    applyUser(id, u) {
      const set = (k, v) => { try { if (v == null) localStorage.removeItem(k); else localStorage.setItem(k, JSON.stringify(v)); } catch (e) { /* noop */ } };
      const s = u.song || {}; set('harmony.mix.v1.' + id, s.mix); set('harmony.loop.v1.' + id, s.loop); set('harmony.lyrics.v1.' + id, s.lyrics); set('harmony.take.v1.' + id, s.take);
      if ('lyricsAuto' in s) set('harmony.lyrics.auto.v1.' + id, s.lyricsAuto); // (v0.14.0) an older user.json has none: the phone's stays
      for (const [k, v] of Object.entries(u.global || {})) if (GLOBAL_KEY.test(k) && localStorage.getItem(k) == null) set(k, v);
      store.set('harmony.pk.userAt.' + id, u.savedAt);
    },
    // a song opened (or just imported): bring the pack and the phone in line, before anything reads its state
    async reconcile(id, open) {
      if (!PKS) return;
      const idx = await getJson('songs/' + id + '/_pack.json'); if (!idx) return;
      if (open) PK.idx = idx;
      const d = PK.dirty()[id] || { user: 0, takes: {} }, out = { applied: false, pulled: 0, marked: 0 };
      if (idx.user) {
        const u = await getJson('songs/' + id + '/user.json');
        if (u && u.savedAt !== store.get('harmony.pk.userAt.' + id) && !d.user) { PK.applyUser(id, u); out.applied = true; }
      } else if (['mix', 'loop', 'lyrics', 'lyrics.auto', 'take'].some((k) => localStorage.getItem('harmony.' + k + '.v1.' + id) != null)) PK.mark(id, { user: true });
      const recs = ((await REC.op('takes', 'readonly', (st) => st.getAll())) || []).filter((t) => t.songId === id);
      const inPack = idx.takes || {};
      for (const tid of Object.keys(inPack)) {
        if (recs.some((t) => t.id === tid) || !inPack[tid].files['take.json']) continue;
        const rec = await getJson('songs/' + id + '/takes/' + tid + '/take.json'); // a take the phone doesn't have (reinstall)
        if (rec && rec.id === tid) { await REC.op('takes', 'readwrite', (st) => st.put(rec), true); out.pulled++; }
      }
      for (const t of recs) {
        const keys = (await REC.op('tchunks', 'readonly', (st) => st.getAllKeys(IDBKeyRange.bound(t.id + ':', t.id + ':￿')))) || [];
        const files = (inPack[t.id] && inPack[t.id].files) || {};
        const miss = keys.filter((k) => !files[PK.fileOf(String(k))]);
        if (!files['take.json']) { PK.mark(id, { take: t.id, json: true }); out.marked++; }
        for (const k of miss) PK.mark(id, { take: t.id, key: String(k) });
        out.marked += miss.length;
        // (v0.7.0) the phone's copy of a chunk goes now: this start read the pack and it holds the chunk, at the same size
        for (const k of keys) { const key = String(k), sz = files[PK.fileOf(key)]; if (!sz || PK.isDirty(id, key)) continue;
          const v = await REC.op('tchunks', 'readonly', (st) => st.get(key)).catch(() => null);
          if (v && v.byteLength === sz) { await REC.op('tchunks', 'readwrite', (st) => st.delete(key)).catch(() => {}); out.released = (out.released || 0) + 1; } }
      }
      E.pkReconcile = Object.assign(E.pkReconcile || {}, { [id]: out });
      return out;
    },
    async chunk(src, k) { // a take chunk that is only in the pack
      const tid = src.split(':')[0], f = PK.fileOf(src + ':' + k), t = PK.idx && PK.idx.takes && PK.idx.takes[tid];
      if (!t || !t.files[f] || !E.song) return undefined;
      const ck = tid + '/' + f; if (PK.cache.has(ck)) return PK.cache.get(ck);
      try { const r = await fetch('songs/' + E.song.id + '/takes/' + tid + '/' + f); if (!r.ok) return undefined;
        const a = new Int16Array(await r.arrayBuffer()); PK.cache.set(ck, a); if (PK.cache.size > 12) PK.cache.delete(PK.cache.keys().next().value); return a;
      } catch (e) { return undefined; }
    },
    async dropTakes(songId, ids) { // the user's explicit delete: out of the pack too (one save)
      const d = PK.dirty(); if (d[songId]) { ids.forEach((t) => delete d[songId].takes[t]); PK.setDirty(d); }
      if (!PKS || !((E.index && E.index.songs) || []).some((s) => s.id === songId)) return { state: 'done' };
      const txn = 'd' + Date.now().toString(36); window.Android.stageBegin(txn);
      const r = await PK.job(window.Android.packCommit(songId, txn, JSON.stringify({ puts: [], dels: ids.map((t) => 'takes/' + t + '/') })));
      PK.log.push({ songId, at: Date.now(), dels: ids.length, ...r });
      for (const t of ids) for (const k of [...PK.cache.keys()]) if (k.startsWith(t + '/')) PK.cache.delete(k);
      if (E.song && songId === E.song.id) PK.idx = await getJson('songs/' + songId + '/_pack.json') || PK.idx;
      return r;
    },
    afterTake() { const f = spaceCheck('take'); packWarnCheck(); return f; },
    want: new Set(), compactLog: [],
    // a compaction rewrites the whole pack: only when nothing plays or records; the Android side also refuses then, and
    // without room for the full copy + FREE_REC_MIN_BYTES left free ("space": tried again after a later save)
    async compactIdle() {
      if (!PKS) return;
      for (const id of [...PK.want]) {
        if (E.playing || REC.on || REC.busy) return;
        const c = await PK.job(window.Android.packCompact(id));
        PK.compactLog.push({ id, at: Date.now(), compacted: !!c.compacted, reason: c.reason || '' }); if (PK.compactLog.length > 30) PK.compactLog.shift();
        if (c.compacted || c.reason === 'nopack' || c.reason === 'space') PK.want.delete(id);
      }
    },
  };
  if (PKS) {
    document.addEventListener('visibilitychange', () => { if (document.visibilityState === 'hidden') PK.flush(); });
    window.addEventListener('pagehide', () => { PK.flush(); });
  }

  // ---- a pack above PACK_WARN_BYTES: pick older takes to delete (nothing goes without the user's confirm) ----
  function packWarnCheck() {
    if (!PKS || !E.song) return;
    const sg = ((E.index && E.index.songs) || []).find((s) => s.id === E.song.id);
    const big = PK.idx && PK.idx.packBytes > PACK_WARN_BYTES;
    if (big) impShow('השיר „' + (sg ? sg.title : '') + '” תופס ' + fmtMB(PK.idx.packBytes) + ' בטלפון (רובו הקלטות). כדאי למחוק הקלטות ישנות: „ספריית שירים” ← „לבחור הקלטות למחיקה”.', 'warn');
  }
  const TK = { id: null };
  async function takesAsk(songId) {
    TK.id = songId;
    const sg = ((E.index && E.index.songs) || []).find((s) => s.id === songId);
    const idx = await getJson('songs/' + songId + '/_pack.json') || { takes: {} };
    const recs = ((await REC.op('takes', 'readonly', (st) => st.getAll())) || []).filter((t) => t.songId === songId);
    for (const tid of Object.keys(idx.takes || {})) { // takes only in the pack (a song not opened on this phone yet)
      if (recs.some((t) => t.id === tid) || !idx.takes[tid].files['take.json']) continue;
      const r = await getJson('songs/' + songId + '/takes/' + tid + '/take.json'); if (r && r.id === tid) recs.push(r);
    }
    recs.sort((a, b) => (a.created || 0) - (b.created || 0));
    $('tkQ').textContent = 'הקלטות של „' + (sg ? sg.title : songId) + '” (' + fmtMB(idx.packBytes || 0) + ' בסך הכול)';
    $('tkList').replaceChildren(...recs.map((t) => { const lab = el('label', 'tk-row'), cb = el('input'); cb.type = 'checkbox'; cb.value = t.id;
      const sz = idx.takes[t.id] ? idx.takes[t.id].bytes : 0, dt = new Date(t.created || 0);
      lab.append(cb, el('span', 'tk-name', t.name), el('span', 'tk-meta', dt.toLocaleDateString('he-IL') + ' · ' + fmtMB(sz))); return lab; }));
    $('tkEmpty').hidden = recs.length > 0; $('tkYes').disabled = true; $('tkConfirm').hidden = true;
    $('tkBox').hidden = false;
  }
  function takesWire() {
    $('tkList').addEventListener('change', () => { const n = $('tkList').querySelectorAll('input:checked').length; $('tkYes').disabled = !n; $('tkYes').textContent = n ? 'מחיקת ' + n + ' הקלטות' : 'מחיקה'; $('tkConfirm').hidden = true; });
    $('tkNo').addEventListener('click', () => { $('tkBox').hidden = true; });
    $('tkYes').addEventListener('click', () => { const n = $('tkList').querySelectorAll('input:checked').length; if (!n) return;
      $('tkConfirmTxt').textContent = 'למחוק ' + n + ' הקלטות לצמיתות? אי אפשר לשחזר אותן.'; $('tkConfirm').hidden = false; });
    $('tkConfirmNo').addEventListener('click', () => { $('tkConfirm').hidden = true; });
    $('tkConfirmYes').addEventListener('click', async () => {
      const ids = [...$('tkList').querySelectorAll('input:checked')].map((c) => c.value), songId = TK.id; $('tkBox').hidden = true;
      if (E.song && songId === E.song.id && (REC.on || REC.busy)) { ui.status('אי אפשר למחוק הקלטות בזמן הקלטה.'); return; }
      for (const id of ids) { await REC.op('takes', 'readwrite', (st) => st.delete(id)); await REC.op('tchunks', 'readwrite', (st) => st.delete(IDBKeyRange.bound(id + ':', id + ':￿'))); }
      if (E.playing) pause(); // (a compaction never runs while audio plays)
      const r = await PK.dropTakes(songId, ids);
      await new Promise((q) => setTimeout(q, 300));
      const c = await PK.job(window.Android.packCompact(songId)); // the space comes back only when the pack is rewritten
      if (!c.compacted) PK.want.add(songId);
      const msg = r.state === 'done' ? ids.length + ' הקלטות נמחקו' + (c.compacted ? '.' : '. כדי לפנות את המקום בפועל צריך עוד מקום פנוי זמני — זה יקרה אוטומטית אחר כך.') : (r.msg || 'המחיקה נכשלה.');
      try { sessionStorage.setItem('harmony.flash', msg); } catch (e) { /* noop */ }
      location.replace(E.song ? '?song=' + encodeURIComponent(E.song.id) : location.pathname);
    });
  }

  function libInit() {
    const btn = $('libBtn'), box = $('lib'), list = $('libList');
    if (!LIB.wired) {
      LIB.wired = true;
      btn.addEventListener('click', () => { box.hidden = !box.hidden; btn.setAttribute('aria-expanded', String(!box.hidden)); });
      list.addEventListener('click', (e) => {
        const del = e.target.closest('.song-del'); if (del) { delAsk(del.dataset.id); return; }
        const tk = e.target.closest('.song-takes'); if (tk) { takesAsk(tk.dataset.id); return; }
        const row = e.target.closest('.song-row'); if (!row || row.disabled || (E.song && row.dataset.id === E.song.id)) return;
        openSong(row.dataset.id);
      });
      if (LIBS) $('libFolderBtn').addEventListener('click', libPick);
      songInit(); // (v0.9.1)
      if (PACKS) {
        $('impBtn').hidden = false;
        [$('impBtn'), $('impBtn2')].forEach((b) => b.addEventListener('click', () => { impShow('בוחרים את קובץ השיר…'); if (LIBS) spaceCheck('import'); window.Android.importPick(); }));
        $('impOpen').addEventListener('click', () => { if (IMP.openId) openSong(IMP.openId); });
        $('delNo').addEventListener('click', delClose);
        $('delYes').addEventListener('click', delDo);
        $('delBox').addEventListener('click', (e) => { if (e.target === $('delBox')) delClose(); });
        impPoll();
      }
    }
    libRender();
  }
  function libRender() {
    const btn = $('libBtn'), list = $('libList'), songs = (E.index && E.index.songs) || [];
    btn.hidden = E.empty || (songs.length < 2 && !PACKS);
    if (btn.hidden) { $('lib').hidden = true; btn.setAttribute('aria-expanded', 'false'); }
    const recBusy = REC.on || REC.busy;
    if (LIBS && E.lib) { // (v0.6.0) where the songs are kept
      $('libFolder').hidden = false;
      $('libFolderTxt').textContent = E.lib.mode === 'folder' ? '📁 השירים, המילים וההקלטות נשמרים בתיקייה ' + E.lib.label : 'השירים וההקלטות נשמרים רק בתוך האפליקציה (אם מוחקים אותה, הם נמחקים איתה).';
      $('libFolderBtn').hidden = E.lib.mode === 'folder';
    }
    const render = () => list.replaceChildren(...songs.map((sg) => {
      const cur = !!E.song && sg.id === E.song.id, stub = sg.audio === false;
      const item = el('div', 'song-item' + (stub ? ' stub' : ''));
      const b = el('button', 'song-row' + (cur ? ' cur' : '')); b.type = 'button'; b.dataset.id = sg.id; b.disabled = stub;
      if (cur) b.setAttribute('aria-current', 'true');
      b.append(el('span', 's-title', sg.title), el('span', 's-dur', stub ? '' : LIB.durs[sg.id] != null ? fmt(LIB.durs[sg.id]) : '…'), el('span', 's-sub', sg.artist));
      if (sg.packBytes != null) { // (v0.6.0) the pack's size and how much of it is takes
        b.append(el('span', 's-size', stub ? 'השיר הוסר מהטלפון · ההקלטות וההגדרות נשמרו (' + fmtMB(sg.packBytes) + ') · כדי לנגן שוב מייבאים את השיר'
          : fmtMB(sg.packBytes) + (sg.takeBytes ? ' · מזה הקלטות ' + fmtMB(sg.takeBytes) : '')));
        if (sg.packBytes > PACK_WARN_BYTES) b.classList.add('big');
      }
      if (sg.tier != null && !stub && TIER_BADGE[sg.tier]) b.append(el('span', 's-tier', TIER_BADGE[sg.tier])); // (v0.11.0) a preview, still being prepared
      item.append(b);
      if (PACKS && !stub) {
        const d = el('button', 'song-del'); d.type = 'button'; d.dataset.id = sg.id; d.disabled = cur && recBusy;
        d.setAttribute('aria-label', 'מחיקת השיר מהטלפון'); d.title = 'מחיקת השיר מהטלפון'; d.append(el('span', null, '🗑️'));
        d.firstChild.setAttribute('aria-hidden', 'true');
        item.append(d);
      }
      if (PKS && sg.packBytes > PACK_WARN_BYTES) { const w = el('button', 'chip warn song-takes', '⚠️ גדול: לבחור הקלטות למחיקה'); w.type = 'button'; w.dataset.id = sg.id; item.append(w); } // (below the row + its 🗑️)
      return item;
    }));
    render();
    Promise.all(songs.filter((sg) => LIB.durs[sg.id] == null && sg.audio !== false).map((sg) => fetch('songs/' + sg.id + '/song.json').then((r) => r.json()).then((m) => { LIB.durs[sg.id] = m.frames / m.sampleRate; }, () => {})))
      .then(render);
  }
  async function libReload() {
    try { const r = await fetch('songs/index.json', { cache: 'no-store' }); const j = r.ok ? await r.json() : null; E.index = { songs: (j && Array.isArray(j.songs)) ? j.songs : [] }; } catch (e) { /* keep the old list */ }
    libRender();
  }

  // ---- import (Android: system picker, or a file opened / shared from another app) ----
  // The native side does the work (streaming unzip, every file's size + sha256 checked, free space checked first, the
  // installed copy replaced only after the new one is complete); the page shows its progress and its verdict. The verdict
  // of an import is shown once (localStorage remembers its token), also across the page reload that opens the new song.
  const IMP = { t: null, openId: null, waitRec: null, hideT: null, started: false, busyUntil: 0 };
  function impShow(txt, kind, prog) {
    const box = $('impBox'); box.hidden = !txt; box.className = 'imp-box' + (kind ? ' ' + kind : '');
    $('impTxt').textContent = txt || '';
    const p = $('impProg'); p.hidden = prog == null; if (prog != null) p.value = prog;
    if (kind !== 'ok') { $('impOpen').hidden = true; IMP.openId = null; }
    clearTimeout(IMP.hideT); if (kind === 'ok') IMP.hideT = setTimeout(() => { if ($('impOpen').hidden) impShow(''); }, 6000);
  }
  function impPoll() {
    clearTimeout(IMP.t);
    if (!IMP.started) { IMP.started = true; $('impBox').addEventListener('click', (e) => { if (e.target.id !== 'impOpen' && !/run/.test($('impBox').className)) impShow(''); });
      let f = null; try { f = sessionStorage.getItem('harmony.flash'); sessionStorage.removeItem('harmony.flash'); } catch (e) { /* noop */ }
      if (f) impShow(f, 'ok'); } // the verdict of the import that opened this page
    let s = null; try { s = JSON.parse(window.Android.importStatus()); } catch (e) { /* bridge gone */ }
    let next = 1000;
    if (s) {
      if (s.busy) { IMP.busyUntil = Date.now() + 5000; if (s.state !== 'running') impShow('ייבוא אחר עדיין רץ. כדאי לחכות שיסתיים ולנסות שוב.', 'warn'); }
      else if (s.cancelled && s.state !== 'running') impShow('');
      if (s.state === 'running') {
        next = 300;
        const pct = s.total > 0 ? Math.min(1, s.done / s.total) : null;
        const busy = IMP.busyUntil > Date.now() ? 'השיר השני לא יובא: אפשר לייבא אותו שוב כשהייבוא הזה יסתיים. ' : ''; // a 2nd file while this one runs
        impShow(busy + (s.title ? 'מייבא את „' + s.title + '”' : 'מייבא שיר') + (pct != null ? ' · ' + Math.floor(pct * 100) + '%' : '…'), busy ? 'run warn' : 'run', pct != null ? pct : 0);
      } else if ((s.state === 'done' || s.state === 'error') && s.token && store.get('harmony.import.seen') !== s.token) {
        store.set('harmony.import.seen', s.token);
        if (s.state === 'error') impShow(s.msg || 'הייבוא נכשל.', 'err');
        else impDone(s);
      } else if (IMP.waitRec && !REC.on && !REC.busy) { const id = IMP.waitRec; IMP.waitRec = null; openSong(id); return; }
      else if (TP.wait && !REC.on && !REC.busy) { TP.wait = false; tierApply(); } // (v0.11.0) the newer version, after the take
    }
    IMP.t = setTimeout(impPoll, next);
  }
  window.harmonyImportPoll = () => { if (PACKS && IMP.started) impPoll(); }; // the Android side: an import just started
  function impDone(s) {
    const same = !!E.song && s.id === E.song.id;
    if (same && (TIER() !== null || s.skipped)) { tierUp(s); return; } // (v0.11.0) a newer version of the open preview: never from 0 (skipped: an older one, refused)
    if (s.via === 'search' && !same && !s.unchanged) tierAuto(s); // (v0.11.0) the first preview of a requested song plays by itself
    if (PKS && !same) PK.reconcile(s.id).then(() => PK.flush()).catch(() => {}); // (v0.6.0) this phone's takes / settings for it -> its pack
    impShow('השיר „' + s.title + '” ' + (s.unchanged ? 'כבר בספרייה (הקובץ תקין, אין מה לעדכן)' : s.replaced ? 'עודכן' : 'נוסף') + ' ✓', 'ok');
    if (REC.on || REC.busy) { // never disturb a recording: the song opens after it stops
      if (same) IMP.waitRec = s.id; else libReload();
      return;
    }
    if (s.via === 'search' && !same && !(E.empty && $('songBox').hidden)) { libReload(); IMP.openId = s.id; $('impOpen').hidden = false; if (!$('songBox').hidden) songRender(); return; } // (v0.9.1) built on the computer: it waits in the library
    if (E.empty || same || !E.playing) { // the new song opens (a re-imported current one reloads)
      try { sessionStorage.setItem('harmony.flash', $('impTxt').textContent); } catch (e) { /* noop */ }
      openSong(s.id); return;
    }
    libReload(); IMP.openId = s.id; $('impOpen').hidden = false; // playing another song: keep playing; open on request
  }

  // ---- (v0.9.1) "🔎 חיפוש שיר": search YouTube, ask the home computer to build the song, follow it, import it ----
  // The native side (SongSearch.kt) does every network call; the page only reads Android.songState() — a snapshot of
  // the relay's jobs for this phone + the download / import of a ready song — and asks for a search / request / cancel.
  const SONGS = ANDROID && typeof window.Android.songState === 'function' && (() => { try { return window.Android.songEnabled(); } catch (e) { return false; } })();
  const SONG = { wired: false, t: null, seq: 0, searchJob: null, s: null, msg: '', share: false, auto: null, keepMsg: false };
  const SONG_STAGE = { download: 'מוריד מיוטיוב', decode: 'מכין את הקול', sep1: 'מפריד את השירה', sep2: 'מפריד את הכלים', combine: 'מרכיב ערוצים',
    stemset: 'מרכיב ערוצים', make: 'בונה את השיר', analysis: 'מנתח אקורדים ומנגינה', pack: 'אורז', upload: 'שולח לטלפון' };
  const SONG_ERR = { nosource: 'לא הצלחתי להוריד את השיר', toolong: 'השיר ארוך מדי', disk: 'אין מספיק מקום במחשב', sep: 'תקלה בהפרדת הכלים',
    analysis: 'תקלה בניתוח השיר', pack: 'תקלה בבניית השיר', timeout: 'העבודה לקחה יותר מדי זמן', worker: 'המחשב הפסיק לענות',
    expired: 'הבקשה ישנה מדי', internal: 'תקלה במחשב', search: 'החיפוש נכשל' };
  const SONG_DISK = '💾 אין מספיק מקום במחשב כרגע, נסו שוב מאוחר יותר'; // (v0.10.0) code=disk: no auto retry
  const songHave = (sid) => !!sid && ((E.index && E.index.songs) || []).some((x) => x.id === sid && x.audio !== false);
  function songInit() {
    if (!SONGS || SONG.wired) return;
    SONG.wired = true;
    document.querySelectorAll('.srch-entry').forEach((b) => { b.hidden = false; b.addEventListener('click', songOpen); });
    $('songClose').addEventListener('click', songClose);
    $('songForm').addEventListener('submit', (e) => {
      e.preventDefault();
      const q = $('songQ').value.trim(); if (!q) { $('songQ').focus(); return; }
      $('songQ').blur(); SONG.searchJob = null; SONG.msg = 'מחפש…'; delete $('songRes').dataset.key; $('songRes').replaceChildren();
      SONG.seq = window.Android.songSearch(q); songRender();
    });
    $('songRes').addEventListener('click', (e) => {
      const b = e.target.closest('button[data-act]'); if (!b) return;
      if (b.dataset.act === 'open') { songClose(); openSong(b.dataset.sid); return; }
      if (b.dataset.act === 'req') { b.disabled = true; SONG.msg = 'שולח את הבקשה…'; SONG.seq = window.Android.songRequest(b.dataset.spec); songRender(); }
    });
    $('songMine').addEventListener('click', (e) => {
      const b = e.target.closest('button[data-act]'); if (!b) return;
      const id = b.dataset.id;
      if (b.dataset.act === 'open') { songClose(); openSong(b.dataset.sid); return; }
      b.disabled = true;
      if (b.dataset.act === 'retry') SONG.seq = window.Android.songRetry(id);
      else if (b.dataset.act === 'cancel') SONG.seq = window.Android.songCancel(id);
    });
    window.harmonySongPoll = () => { if (!$('songBox').hidden) songRender(); };
    window.harmonyShare = songShare; songShare(); // (vc38) a song shared before the page was ready
  }
  // (vc38) a song shared as text (Shazam "share" -> הרמוניה): search it and request the top match at once; the fast tier
  // then plays it by itself (tierAuto: the sheet is open). The native side has already turned the text into a query.
  function songShare() {
    let q = ''; try { q = window.Android.shareTake() || ''; } catch (e) { return; }
    if (!q) return;
    $('songQ').value = q; songOpen(); // (the value first: songOpen focuses an empty field = the keyboard)
    SONG.searchJob = null; SONG.auto = null; SONG.share = true; SONG.msg = 'מחפש את „' + q + '”…';
    delete $('songRes').dataset.key; $('songRes').replaceChildren();
    SONG.seq = window.Android.songSearch(q); songRender();
  }
  function songAutoPick(sj, res, vids) { // (vc38) the shared song's search: its first usable result, once
    SONG.auto = null;
    if (sj.state !== 'results') return;
    const r = res.find((x) => !x.long);
    if (!r) { SONG.msg = 'לא מצאתי את השיר ששיתפת. אפשר לבחור מהרשימה או לחפש שם אחר.'; return; }
    if (songHave(r.sid)) { songClose(); openSong(r.sid); return; }
    if (vids.has(r.vid) && vids.get(r.vid).state !== 'error') return; // already asked: it is under "my requests"
    SONG.msg = 'מכין את „' + r.title + '”: יתחיל להתנגן בעוד כמה שניות…';
    SONG.seq = window.Android.songRequest(JSON.stringify({ vid: r.vid, title: r.title, channel: r.channel, dur: r.dur }));
    SONG.keepMsg = true;
  }
  function songOpen() {
    $('songBox').hidden = false; $('lib').hidden = true; $('libBtn').setAttribute('aria-expanded', 'false');
    try { window.Android.songSheet(true); } catch (e) { /* noop */ }
    songRender(); clearInterval(SONG.t); SONG.t = setInterval(songRender, 1000);
    if (!$('songQ').value) setTimeout(() => $('songQ').focus(), 50);
  }
  function songClose() {
    $('songBox').hidden = true; clearInterval(SONG.t); SONG.t = null;
    try { window.Android.songSheet(false); } catch (e) { /* noop */ }
  }
  function songRender() {
    let s = null; try { s = JSON.parse(window.Android.songState()); } catch (e) { return; }
    SONG.s = s;
    const jobs = s.jobs || [], op = s.op || {};
    if (op.seq && op.seq === SONG.seq && op.state !== 'running') {
      SONG.seq = 0;
      if (op.state === 'error') { SONG.msg = op.msg || 'משהו השתבש.'; SONG.share = false; SONG.keepMsg = false; }
      else if (op.kind === 'search') { SONG.searchJob = op.job; if (SONG.share) { SONG.share = false; SONG.auto = op.job; } else SONG.msg = ''; }
      else if (op.kind === 'request') { if (SONG.keepMsg) SONG.keepMsg = false; else SONG.msg = op.dedup ? 'כבר ביקשת את השיר הזה: הוא ברשימה למטה.' : 'הבקשה נשלחה ✓'; }
      else SONG.msg = '';
    }
    if (!SONG.searchJob) { const last = jobs.find((j) => j.kind === 'search'); if (last && !SONG.seq && !SONG.msg) SONG.searchJob = last.id; }
    const sj = SONG.searchJob && jobs.find((j) => j.id === SONG.searchJob);
    const reqs = jobs.filter((j) => j.kind === 'request');
    const openReq = reqs.some((j) => ['queued', 'running', 'uploading'].includes(j.state));
    $('songNet').hidden = !s.offline;
    $('songOff').hidden = s.offline || !s.workerOff || !openReq;
    let sMsg = '';
    if (sj) {
      if (sj.state === 'results') sMsg = (sj.results || []).length ? '' : 'לא נמצאו שירים. אפשר לנסות שם אחר.';
      else if (sj.state === 'error') sMsg = 'החיפוש לא הצליח. אפשר לנסות שוב.';
      else sMsg = s.workerOff ? 'המחשב כבוי: החיפוש יתחיל כשהוא יידלק.' : 'מחפש…';
    }
    // the results (only the newest search's)
    const vids = new Map(reqs.map((j) => [j.vid, j]));
    const res = sj && sj.state === 'results' ? sj.results || [] : [];
    if (SONG.auto && sj && sj.id === SONG.auto && (sj.state === 'results' || sj.state === 'error')) songAutoPick(sj, res, vids);
    const key = JSON.stringify([res.map((r) => r.vid), res.map((r) => songHave(r.sid)), [...vids.keys()], reqs.map((j) => j.state)]);
    if ($('songRes').dataset.key !== key) {
      $('songRes').dataset.key = key;
      $('songRes').replaceChildren(...res.map((r) => {
        const row = el('div', 'song-row2');
        const img = el('img', 'song-thumb'); img.alt = ''; if (/^data:image\/jpeg;base64,/.test(r.thumb || '')) img.src = r.thumb; row.append(img);
        row.append(el('span', 'song-t', r.title), el('span', 'song-s', (r.channel || '') + (r.dur ? ' · ⁦' + fmt(r.dur) + '⁩' : '')));
        const act = el('div', 'song-act'), mine = vids.get(r.vid);
        if (songHave(r.sid)) { const b = el('button', 'chip', 'כבר בספרייה ▶️'); b.type = 'button'; b.dataset.act = 'open'; b.dataset.sid = r.sid; act.append(b); }
        else if (r.long) act.append(el('span', 'song-tag warn', 'ארוך מדי (עד 9 דקות)'));
        else if (mine && mine.state !== 'error') act.append(el('span', 'song-tag ok', 'ביקשת: ראו „הבקשות שלי”'));
        else { const b = el('button', 'chip', '⬇️ להוסיף לספרייה'); b.type = 'button'; b.dataset.act = 'req';
          b.dataset.spec = JSON.stringify({ vid: r.vid, title: r.title, channel: r.channel, dur: r.dur }); act.append(b); }
        row.append(act); return row;
      }));
    }
    $('songMsg').textContent = SONG.msg || sMsg; // (vc38: after the auto pick, which sets its own message)
    // my requests
    $('songMineH').hidden = !reqs.length;
    $('songMine').replaceChildren(...reqs.map((j) => {
      const row = el('div', 'song-row2'), L = j.local || {};
      const sid = (j.blob && j.blob.songId) || L.songId || '';
      row.append(el('span', 'song-thumb'), el('span', 'song-t', j.title || ''), el('span', 'song-s', j.channel || ''));
      const act = el('div', 'song-act'), btn = (txt, a) => { const b = el('button', 'chip', txt); b.type = 'button'; b.dataset.act = a; b.dataset.id = j.id; if (sid) b.dataset.sid = sid; return b; };
      const tag = (txt, k) => el('span', 'song-tag' + (k ? ' ' + k : ''), txt);
      const prog = (v) => { const p = el('progress', 'song-prog'); p.max = 100; p.value = v || 0; return p; };
      if (j.state === 'done' || L.state === 'done') {
        if (sid && songHave(sid)) act.append(btn('✅ נוסף לספרייה ▶️', 'open')); else act.append(tag('✅ נוסף לספרייה', 'ok'));
      } else if (L.state === 'error') act.append(tag('❌ לא הצליח: ' + (L.msg || 'הייבוא נכשל'), 'err'), btn('🔁 לנסות שוב', 'retry'));
      else if (L.state === 'importing') act.append(tag('מייבא…'));
      else if (L.state === 'downloading') act.append(tag('מוריד… ' + (L.pct || 0) + '%'), prog(L.pct));
      else if (j.state === 'ready') act.append(tag('מוכן: מוריד לטלפון…'));
      else if (j.state === 'queued') act.append(tag(j.pos ? 'בתור (מקום ' + j.pos + ')' : 'בתור'), btn('ביטול', 'cancel'));
      else if (j.state === 'running' || j.state === 'uploading') {
        const st = j.state === 'uploading' ? 'שולח לטלפון' : SONG_STAGE[j.stage] || 'מתחיל';
        act.append(tag('בעבודה: ' + st + (j.pct != null ? ' · ' + j.pct + '%' : '')));
        if (j.etaS) act.append(tag('עוד כ־' + Math.max(1, Math.ceil(j.etaS / 60)) + ' דק\''));
        act.append(prog(j.pct));
      } else if (j.state === 'error') act.append(tag(j.code === 'disk' ? SONG_DISK : '❌ לא הצליח: ' + (SONG_ERR[j.code] || 'תקלה'), 'err'), ...(j.code === 'toolong' ? [] : [btn('🔁 לנסות שוב', 'retry')]), btn('הסרה', 'cancel')); // (v0.10.0) disk: the computer refused / stopped the job for space; retry is by hand only
      row.append(act); return row;
    }));
    backSync();
  }

  // ---- delete (its audio only) ----
  const DEL = { id: null };
  function delAsk(id) {
    const sg = ((E.index && E.index.songs) || []).find((x) => x.id === id); if (!sg) return;
    if (E.song && id === E.song.id && (REC.on || REC.busy)) { ui.status('אי אפשר למחוק את השיר בזמן הקלטה.'); return; }
    DEL.id = id; $('delQ').textContent = 'למחוק את השיר „' + sg.title + '” מהטלפון?';
    $('delBox').hidden = false; $('delNo').focus();
  }
  function delClose() { $('delBox').hidden = true; DEL.id = null; }
  async function delDo() {
    const id = DEL.id; delClose(); if (!id) return;
    const cur = !!E.song && id === E.song.id, was = E.playing;
    if (cur && was) pause();
    if (cur) await PK.flush(); // this song's last changes go into its pack first
    impShow('מוחק את השיר…', 'run');
    let r = null; try { const j = window.Android.songDelete(id); r = /^j\d+$/.test(j) ? await PK.job(j) : JSON.parse(j); } catch (e) { r = null; }
    if (!r || !r.ok) { impShow((r && r.msg) || 'לא הצלחתי למחוק את השיר.', 'err'); return; }
    const rest = ((E.index && E.index.songs) || []).filter((x) => x.id !== id && x.audio !== false);
    E.index = { songs: ((E.index && E.index.songs) || []).map((x) => (x.id === id ? { ...x, audio: false } : x)) };
    if (cur) { // the open song is gone: the next one, or the empty screen
      if (store.get('harmony.lastSong') === id) store.set('harmony.lastSong', rest.length ? rest[0].id : null);
      try { sessionStorage.setItem('harmony.flash', 'השיר נמחק מהטלפון. ההקלטות וההגדרות שלו נשמרו.'); } catch (e) { /* noop */ }
      setTimeout(() => location.replace(rest.length ? '?song=' + encodeURIComponent(rest[0].id) : '?'), was ? FADE_OUT * 1000 + 60 : 0);
      return;
    }
    impShow('השיר נמחק מהטלפון. ההקלטות וההגדרות שלו נשמרו.', 'ok');
    libReload();
  }
  function emptyState() { // no song installed (a fresh install, or every song deleted)
    E.empty = true;
    document.body.classList.add('no-songs');
    $('title').textContent = ''; $('title').hidden = true; $('artist').textContent = '';
    $('empty').hidden = false; $('impBtn2').hidden = !PACKS; $('emptyImp').hidden = !PACKS; // (a browser: no import)
    if (E.index.songs.length) $('emptyH').textContent = 'אין כרגע שירים בספרייה'; // (every song deleted: their takes are kept)
    ui.status('');
    libInit();
  }
  function openSong(id) {
    store.set('harmony.lastSong', id);
    const nav = () => location.replace('?song=' + encodeURIComponent(id));
    const go = () => { if (!PKS) { nav(); return; } let left = true; const fin = () => { if (left) { left = false; nav(); } }; PK.flush().then(fin, fin); setTimeout(fin, 4000); }; // (v0.6.0) pending saves first
    if (E.playing) {
      try { sessionStorage.setItem('harmony.autoplay', '1'); } catch (e) { /* noop */ }
      fadeOut(); setTimeout(go, FADE_OUT * 1000 + 30); // silent before the page (and its audio) goes
    } else go();
  }

  // ---- (v0.11.0) progressive song: a requested song arrives in versions (PROGRESSIVE.md §4). song.json "tier": 0 = the
  // song as one channel, 1 = vocals + accompaniment, 2 = every instrument; no "tier" = the full version (chords, melody).
  // The open preview shows what is still being prepared (Android.songState(), matched by the song id); a newer version
  // reloads at the same spot: paused by itself, playing behind one tap, never during a take. Songs without "tier": none of this.
  const TIER_NAME = ['גרסה מקדימה', 'גרסה עם שירה וליווי', 'גרסה עם כל הכלים']; // (+ null: 'הגרסה המלאה')
  const TIER_BADGE = ['🎧 גרסה מקדימה: השיר בלבד', '🎤 גרסה מקדימה: שירה וליווי', '🎛 גרסה מקדימה: כל הכלים, בלי אקורדים'];
  const TP = { t: null, wait: false, name: '', seq: 0, msg: '' };
  const TIER = () => (E.song && E.song.tier != null && Number.isFinite(+E.song.tier) ? +E.song.tier : null);
  const tierOfJson = (m) => (m && m.tier != null && Number.isFinite(+m.tier) ? +m.tier : null);
  const tierJob = (s, id) => ((s && s.jobs) || []).filter((j) => j.kind === 'request' && (j.sid || (j.tier && j.tier.songId) || (j.blob && j.blob.songId) || (j.local && j.local.songId)) === id)
    .sort((a, b) => (b.created || 0) - (a.created || 0))[0] || null;
  function tierInit() {
    if (TIER() === null) return;
    tierHints(); tierPoll();
    $('prepRetry').addEventListener('click', () => { const b = $('prepRetry'); if (!b.dataset.id) return; b.disabled = true; TP.msg = 'שולח את הבקשה…'; TP.seq = window.Android.songRetry(b.dataset.id); tierPoll(); });
    $('tierUp').addEventListener('click', () => { const b = $('tierUp'); b.hidden = true; if (REC.on || REC.busy) { TP.wait = true; return; } tierReload(); }); // (a take started meanwhile: after it)
    if (SONGS) TP.t = setInterval(tierPoll, 2000); // a bridge read (no network): the native side polls the relay
  }
  function tierHints() {
    if (TIER() === null) return;
    $('harmPrep').hidden = !!HV.A;
    $('pvPrep').hidden = !!PV.ref;
  }
  function tierPoll() {
    if (TIER() === null) return;
    let s = null; if (SONGS) try { s = JSON.parse(window.Android.songState()); } catch (e) { s = null; }
    const j = tierJob(s, E.song.id), L = (j && j.local) || {}, op = (s && s.op) || {};
    if (TP.seq && op.seq === TP.seq && op.state !== 'running') { TP.seq = 0; TP.msg = op.state === 'error' ? op.msg || 'משהו השתבש.' : ''; $('prepRetry').disabled = false; }
    const eta = (j && j.etaS) ? ' · עוד כ־' + Math.max(1, Math.ceil(j.etaS / 60)) + ' דק\'' : '';
    let txt = '', err = false, retry = null;
    if (!j) txt = s ? 'גרסה חלקית: הגרסה המלאה עוד לא הגיעה' : 'גרסה חלקית: חלק מהערוצים, בלי אקורדים';
    else if (L.state === 'error') { txt = 'גרסה חלקית · ' + (L.msg || 'הייבוא נכשל'); err = true; retry = j.id; }
    else if (j.state === 'error') { txt = 'גרסה חלקית · ' + (j.code === 'disk' ? SONG_DISK : SONG_ERR[j.code] || 'תקלה'); err = true; if (j.code !== 'toolong' && j.code !== 'disk') retry = j.id; }
    else if (L.state === 'downloading') txt = 'הגרסה המלאה מגיעה לטלפון · ' + (L.pct || 0) + '%';
    else if (L.state === 'importing' || L.state === 'done' || j.state === 'ready' || j.state === 'done') txt = 'הגרסה המלאה מגיעה לטלפון…';
    else if (j.state === 'queued') txt = 'בהכנה: בתור' + (j.pos ? ' (מקום ' + j.pos + ')' : '');
    else if (j.state === 'uploading') txt = 'בהכנה: שולח לטלפון' + eta;
    else txt = 'בהכנה: ' + (SONG_STAGE[j.stage] || 'מתחיל') + (j.pct != null ? ' · ' + j.pct + '%' : '') + eta;
    if (s && s.offline && !err) txt += ' · אין חיבור לרשת';
    else if (s && s.workerOff && j && ['queued', 'running'].includes(j.state)) txt += ' · המחשב כבוי: ההכנה תמשיך כשיידלק';
    if (TP.msg) txt += ' · ' + TP.msg;
    $('prepTxt').textContent = txt; $('prep').classList.toggle('err', err); $('prep').hidden = false;
    const b = $('prepRetry'); b.hidden = !retry; if (retry) b.dataset.id = retry; else delete b.dataset.id;
  }
  // a newer version of the open preview was imported (same song id; the import never takes an older one, D3)
  function tierUp(s) {
    libReload();
    if (s.unchanged) return; // the same or an older version: nothing changes
    const cur = TIER();
    fetch(E.base + 'song.json', { cache: 'no-store' }).then((r) => (r.ok ? r.json() : null)).catch(() => null).then((m) => {
      const n = m ? tierOfJson(m) : cur + 1; // (unreadable: assume newer, the import said so)
      if (n !== null && n <= cur) return;
      TP.name = n === null ? 'הגרסה המלאה' : TIER_NAME[n] || 'גרסה חדשה';
      if (REC.on || REC.busy) { TP.wait = true; return; } // never during a take: after it stops (impPoll)
      tierApply();
    });
  }
  function tierApply() {
    if (E.playing) { const b = $('tierUp'); b.textContent = '✨ ' + TP.name + ' מוכנה — לעבור'; b.hidden = false; return; }
    try { sessionStorage.setItem('harmony.flash', '✨ ' + TP.name + ' נטענה, מאותו מקום'); } catch (e) { /* noop */ }
    tierReload();
  }
  function tierReload() {
    try { sessionStorage.setItem('harmony.resumeAt', JSON.stringify({ id: E.song.id, sec: posF() / E.SR })); } catch (e) { /* noop */ }
    openSong(E.song.id); // (playing: it sets harmony.autoplay and fades out first)
  }
  // the first preview (tier 0) of a song asked for in the search: it opens and plays, if nothing else is going on
  function tierAuto(s) {
    let j = null; if (SONGS) try { j = tierJob(JSON.parse(window.Android.songState()), s.id); } catch (e) { j = null; }
    const young = !!(j && j.created && Date.now() - j.created < 180000);
    if ((!young && $('songBox').hidden) || (E.empty && $('songBox').hidden)) return; // (the empty screen opens it anyway)
    fetch('songs/' + encodeURIComponent(s.id) + '/song.json', { cache: 'no-store' }).then((r) => (r.ok ? r.json() : null)).catch(() => null).then((m) => {
      if (tierOfJson(m) !== 0 || E.playing || REC.on || REC.busy) return;
      if (!$('songBox').hidden) songClose();
      try { sessionStorage.setItem('harmony.autoplay', '1'); sessionStorage.setItem('harmony.flash', $('impTxt').textContent); } catch (e) { /* noop */ }
      openSong(s.id);
    });
  }

  // ---------------------------------------------------------------- boot
  function frames() { // song frames -> context frames
    const r = E.SR / E.song.sampleRate, sec = (f) => Math.round(f * r);
    E.Lf = sec(E.song.chunkFrames); E.Xf = sec(E.song.xfadeFrames); E.Mf = sec(E.song.marginFrames);
    E.durF = Math.floor(E.song.frames * r);
  }
  async function boot() {
    ui.status('טוען…');
    prInit(); // (v0.10.1) practice needs no song: wired before the folder gate and the empty screen (it was song-only)
    // (v0.6.0) the installed songs; none = the empty screen (how to import). A missing index = none.
    if (!libGate()) return; // (v0.6.0) first start: where the songs live; a folder that can't be reached: say so
    let idx = null;
    try { const r = await fetch('songs/index.json', { cache: 'no-store' }); idx = r.ok ? await r.json() : null; } catch (e) { idx = null; }
    const playable = idx && Array.isArray(idx.songs) ? idx.songs.filter((s) => s.audio !== false) : []; // (a deleted song's pack keeps its takes / settings)
    if (!playable.length) { E.index = { songs: (idx && idx.songs) || [] }; emptyState(); return; }
    try {
      const want = new URLSearchParams(location.search).get('song') || store.get('harmony.lastSong');
      const pick = playable.find((s) => s.id === want) || playable[0];
      store.set('harmony.lastSong', pick.id);
      E.index = idx;
      E.base = 'songs/' + pick.id + '/';
      E.song = await (await fetch(E.base + 'song.json')).json();
      try { await PK.reconcile(pick.id, true); } catch (e) { PK.err = String(e); } // (v0.6.0) the pack's settings / takes first
      await REC.init(); // the active take (if any) joins the stems as the "ההקלטה שלי" channel
      E.ctx = makeCtx();
      E.SR = E.ctx.sampleRate;
      frames();
      buildGraph();
      loadMix();
      applyGains(0);
      ui.build();
      vaInit(); // (v0.7.0)
      cpInit(); // (v0.9.0)
      mediaSession();
      const lyrP = fetch(E.base + 'lyrics.json').then((r) => (r.ok ? r.json() : null)).then(lyPack).catch(() => null); // (lane L) optional
      const lkP = fetch(E.base + 'lyrics-lookup.json').then((r) => (r.ok ? r.json() : null)).catch(() => null); // (v0.14.0) optional: found by name
      fetch(E.base + 'analysis.json').then((r) => (r.ok ? r.json() : null)).catch(() => null).then((A) => Promise.all([lyrP, lkP]).then(([p, q]) => { LY.pack = p; LY.lookF = q; harmInit(A); if (!HV.A) lyInit(); }), () => {}).then(() => { // optional
        PV.ref = null; PV.res = null; PV.song = E.song.id; pvSync(); pvClear();
        return fetch(E.base + 'melody.json').then((r) => (r.ok ? r.json() : null)).then((j) => { if (PV.song !== E.song.id || !j || !window.HarmonyPitch) return; PV.ref = window.HarmonyPitch.melody(j); pvUpdate(); vaUpdate(); }); // (v0.7.0) the active take's analysis / line scores
      }).catch(() => {}).then(tierHints); // (v0.4.8) reference melody for the pitch view, optional
      tierInit(); // (v0.11.0) a progressive preview: what is still being prepared
      await calibrate();
      await loadChunk(0);
      tick();
      ui.status('');
      $('play').disabled = false; $('miniPlay').disabled = false; $('miniStop').disabled = false;
      E.ready = true;
      libInit();
      if (LIBS) { spaceCheck('start'); packWarnCheck(); takesWire();
        setTimeout(async () => { for (const s of idx.songs) if (s.id !== pick.id && !s.user) await PK.reconcile(s.id).catch(() => {}); PK.flush(); }, 2500); } // (v0.6.0) vc27 data of the other songs into their packs
      setTimeout(() => REC.recleanOld(), 1500); // (v0.5.1) this song's speaker takes cleaned by an older version: redo them
      if (ANDROID) try { window.Android.setState(false); } catch (e) { /* old bridge */ } // fresh page: nothing plays yet
      let auto = false; try { auto = sessionStorage.getItem('harmony.autoplay') === '1'; sessionStorage.removeItem('harmony.autoplay'); } catch (e) { /* noop */ }
      let at = null; try { at = JSON.parse(sessionStorage.getItem('harmony.resumeAt')); sessionStorage.removeItem('harmony.resumeAt'); } catch (e) { /* noop */ }
      if (at && at.id === E.song.id && Number.isFinite(at.sec) && at.sec > 0) seek(at.sec); // (v0.11.0) a newer version: from the same spot
      if (auto) play(); // switched songs while playing: keep playing
    } catch (e) {
      ui.status('לא הצלחתי לטעון את השיר. כדאי לנסות שוב.');
      E.bootError = String(e);
      return;
    }
    setInterval(() => { if (E.playing) { tick(); ui.media(false); } else if (!E.released && isHidden() && !E.idleSince) idleCheck(); }, TICK_MS);
    document.addEventListener('visibilitychange', idleCheck);
    document.addEventListener('visibilitychange', () => { if (document.visibilityState === 'hidden' && !REC.on && !REC.busy) REC.closeMic(); });
    idleCheck();
    requestAnimationFrame(frame);
  }

  // native (notification / lock screen / headset) control entry point for the Android wrapper
  // background(true/false): the Android activity's onStop / onStart (the page itself may still count as visible)
  // ================================================================ live practice 🏋️ (v0.8.0)
  // A practice screen over the app. A target tone (the "drone", practice-worklet.js) plays; the microphone's pitch is
  // measured live (practice-pitch.js, every 10 ms) and shown against it: a needle (green ±25 cents, yellow ±50), the
  // time held in tune, a score. Four exercises, all set from the singer's own range (the voice report's; a safe
  // middle range when there are no takes yet): long tones, sirens, scale steps, a steady "ssss" breath.
  // With the phone's speaker the drone's echo is predicted and subtracted from the mic (see the worklet); headphones are
  // still best. Sessions are kept on the phone (IndexedDB, durable) and in the song pack's user part (with the device
  // settings), with a small progress chart per exercise. The mic's audio is not kept unless ⏺ is on.
  const PR_KINDS = { long: '🎯 צליל ארוך', sirens: '〰️ סירנות', scale: '🎼 סולם', breath: '🌬️ נשימה' };
  const PR_HOW = {
    long: 'מקשיבים לצליל, ואז שרים אותו ("אָה" או "מממ") ומחזיקים אותו בדיוק כמה שיותר זמן. אחרי כל צליל עוברים לבא.',
    sirens: 'גלישה רכה מהצליל הנמוך לגבוה וחזרה, לפי הקו. פעם ראשונה רק מקשיבים, אחר כך שלוש פעמים שרים.',
    scale: 'דו-רה-מי למעלה ולמטה. כל צליל: מקשיבים, שרים ומחזיקים שנייה וחצי בטון.',
    breath: 'שאיפה, ואז "ססס" ארוך ואחיד ככל האפשר. בלי צליל: רק הנשיפה.',
  };
  const PR_EX = { sirens: 'sirens', lipTrills: 'sirens', longTones: 'long', humAttack: 'long', targetStart: 'long', listenFirst: 'long', support: 'breath', breath48: 'breath' };
  const PR_KEY = 'harmony.practice.v1', PR_CFG = 'harmony.prcfg.v1', PR_RANGE = 'harmony.vrange.v1', PR_GREEN = 25, PR_YELLOW = 50, PR_GRACE_S = 0.1, PR_HOP = 480; // (PR_HOP: the analysis step, 10 ms — practice-pitch.js)
  const PR = { kind: 'long', run: null, sessions: null, worker: null, node: null, src: null, out: null, ctx: null, raf: 0, lat: [], noteIdx: 0, last: null };
  const prCfg = () => Object.assign({ hold: 10, breath: 20, level: 0.35, oct: 0 }, store.get(PR_CFG) || {});
  const prSet = (p) => store.set(PR_CFG, Object.assign(prCfg(), p));
  const m2c = (m) => (m - 33) * 100, c2hz = (c) => 55 * Math.pow(2, c / 1200), pName = (c) => HVo().noteName(c / 100 + 33);
  function prRange() {
    const r = VA.range || store.get(PR_RANGE), ok = r && Number.isFinite(r.lo) && Number.isFinite(r.hi) && r.hi - r.lo >= 5;
    return ok ? { lo: Math.round(r.lo), hi: Math.round(r.hi), measured: true } : { lo: 57, hi: 64, measured: false }; // (A3–E4: a middle range)
  }
  function prPlan(kind) { // the targets (cents above 55 Hz), from the range and the octave setting
    const r = prRange(), o = 12 * (prCfg().oct || 0), lo = r.lo + o, hi = r.hi + o;
    if (kind === 'long') { const n = []; for (let i = 0; i < 5; i++) { const m = Math.round(lo + 1 + i * (hi - lo - 2) / 4); if (!n.includes(m)) n.push(m); } return { notes: n.map(m2c), r, lo, hi }; }
    if (kind === 'scale') { const t = hi - lo >= 12 ? lo + Math.floor((hi - lo - 12) / 2) : lo, up = [0, 2, 4, 5, 7, 9, 11, 12], dn = [11, 9, 7, 5, 4, 2, 0]; return { notes: [...up, ...dn].map((d) => m2c(t + d)), tonic: m2c(t), r, lo, hi }; }
    if (kind === 'sirens') return { from: m2c(lo + 1), to: m2c(hi - 1), r, lo, hi };
    return { r, lo, hi };
  }
  function prMode() { return window.__PR_MODE || (REC.mode === 'speaker' ? 'speaker' : 'headphones'); }
  async function prSessions() {
    if (PR.sessions) return PR.sessions;
    let a = []; try { a = (await REC.op('tchunks', 'readonly', (st) => st.get('pr:sessions'))) || []; } catch (e) { a = []; }
    const m = new Map(); [...(Array.isArray(a) ? a : []), ...(store.get(PR_KEY) || [])].forEach((x) => { if (x && x.id) m.set(x.id, x); });
    PR.sessions = [...m.values()].sort((x, y) => x.at - y.at); return PR.sessions;
  }
  async function prSave(s) { // durable on the phone first (IndexedDB), then the pack's user part (device settings), saved now
    const all = await prSessions(); all.push(s); while (all.length > 300) all.shift();
    try { await REC.op('tchunks', 'readwrite', (st) => st.put(all, 'pr:sessions')); } catch (e) { /* no IndexedDB */ }
    store.set(PR_KEY, all.slice(-200));
    if (PKS) { clearTimeout(PK.t); PK.flush(); }
  }
  // ---- the audio: one worklet (drone out, mic in, echo removed) -> the pitch Worker; the page gets its results
  function prCtx() { // (v0.10.1) the song's context; with no song loaded (an empty library) one of its own, made in the tap
    if (E.released) revive(); else if (!E.ctx) { E.ctx = makeCtx(); E.SR = E.ctx.sampleRate; }
    return E.ctx;
  }
  async function prAudio() {
    const ctx = prCtx(); await ctx.resume();
    if (PR.ctx !== ctx) { PR.ctx = ctx; PR.node = null; PR.modP = ctx.audioWorklet.addModule('practice-worklet.js'); }
    await PR.modP;
    if (!PR.worker) { const src = await (await fetch('practice-pitch.js')).text(); PR.worker = new Worker(URL.createObjectURL(new Blob([src], { type: 'application/javascript' }))); PR.worker.onmessage = (e) => prFrame(e.data); }
    if (!PR.node) {
      PR.node = new AudioWorkletNode(ctx, 'harmony-practice', { numberOfInputs: 1, numberOfOutputs: 1, outputChannelCount: [1] });
      PR.out = ctx.createGain(); PR.out.gain.value = 1; PR.node.connect(PR.out); PR.out.connect(ctx.destination);
      const ch = new MessageChannel(); PR.node.port.postMessage({ worker: ch.port1 }, [ch.port1]); PR.worker.postMessage({ port: ch.port2 }, [ch.port2]);
      PR.node.port.onmessage = (e) => prPort(e.data);
    }
    if (PR.src) { try { PR.src.disconnect(); } catch (e) { /* gone */ } PR.src = null; }
    if (window.__PR_SRC) { PR.src = window.__PR_SRC; PR.src.connect(PR.node); return true; } // (tests: a synthetic voice)
    if (!(await REC.ensureMode())) return false;
    try { const m = await REC.mic(); PR.mic = m; PR.src = ctx.createMediaStreamSource(m.stream); PR.src.connect(PR.node); } catch (e) { ui.status('אין גישה למיקרופון'); return false; }
    return true;
  }
  function prDrone(cmd) { if (PR.node) PR.node.port.postMessage(cmd); }
  function prPort(m) {
    const R = PR.run; if (!R) return;
    if (m.learned) { R.learned.push(m.learned); R.gateFrom = m.learned.at; }
    if (m.raw && R.rec) R.rec.push(m.raw);
  }
  // ---- a run: the exercise planned ahead on the context clock; every analysis frame is scored against it
  const prNow = () => Math.round(PR.ctx.currentTime * E.SR);
  function prStart() {
    const kind = PR.kind, cfg = prCfg(), plan = prPlan(kind), SR = E.SR, mode = prMode(), t0 = prNow() + Math.round(0.25 * SR), level = cfg.level;
    const R = PR.run = { id: 'p' + Date.now().toString(36), kind, plan, cfg, mode, at: Date.now(), t0, steps: [], learned: [], frames: [], gateDb: -55, gateFrom: 0, done: false, rec: PR.recOn ? [] : null, paint: [] };
    const fmin = c2hz(Math.min(plan.lo == null ? 4000 : m2c(plan.lo), 4000) - 400);
    PR.worker.postMessage({ cfg: { fmin: Math.max(65, Math.min(fmin, 200)), fmax: 1100, gateDb: -60 } });
    prDrone({ record: !!R.rec });
    let t = t0;
    if (kind === 'long' || kind === 'scale') {
      const listen = kind === 'long' ? 1.0 : 0.8, need = kind === 'long' ? cfg.hold : 1.5, maxSing = kind === 'long' ? cfg.hold + 10 : 6;
      const notes = kind === 'long' ? plan.notes.slice(Math.min(PR.noteIdx, plan.notes.length - 1)) : plan.notes;
      notes.forEach((c) => { const st = { target: c, listenF: t, singF: t + Math.round(listen * SR), endF: t + Math.round((listen + maxSing) * SR), need, hold: { s: -1, l: -1, best: 0 }, n: 0, nIn: 0, nV: 0 };
        prDrone({ at: t, drone: { hz: c2hz(c), level } });
        if (mode === 'speaker' && level > 0) prDrone({ at: t + Math.round(0.2 * SR), learn: Math.round((listen - 0.5) * SR) }); // (fit 0.2 s in; the last 0.3 s of the drone alone sets the floor)
        R.steps.push(st); t = st.endF + Math.round(0.4 * SR); });
      prDrone({ at: t, drone: { level: 0 } }); R.endF = t;
    } else if (kind === 'sirens') {
      const G = 4 * SR, segs = [];
      prDrone({ at: t, drone: { hz: c2hz(plan.from), level } });
      for (let p = 0; p < 4; p++) { // pass 0 = listen (the guide alone), 1–3 = sing (guide on with headphones only)
        const lvl = p === 0 || mode === 'headphones' ? level : 0;
        prDrone({ at: t, drone: { level: lvl } });
        prDrone({ at: t, drone: { glide: { to: c2hz(plan.to), frames: G, shape: 'cos' } } }); segs.push({ a: t, b: t + G, from: plan.from, to: plan.to, sing: p > 0 });
        prDrone({ at: t + G, drone: { glide: { to: c2hz(plan.from), frames: G, shape: 'cos' } } }); segs.push({ a: t + G, b: t + 2 * G, from: plan.to, to: plan.from, sing: p > 0 });
        t += 2 * G + Math.round(0.5 * SR);
      }
      prDrone({ at: t, drone: { level: 0 } }); R.segs = segs; R.endF = t;
      R.latF = window.__PR_LAT != null ? window.__PR_LAT : REC.latencyF(); // the voice follows what it HEARD: compare it with the target that long ago
      R.sing = []; // [t, err] of voiced sing frames (the lag search at the end)
    } else { // breath: no tone; 1.5 s of quiet (the room's floor), then one long "ssss"
      prDrone({ at: t, drone: { level: 0 } });
      R.floorF = t + Math.round(1.5 * SR); R.endF = t + Math.round((cfg.breath + 25) * SR); R.br = { floor: [], start: -1, last: -1, dbs: [] };
    }
    R.timer = setInterval(prTick, 50);
    prUI();
  }
  function prTargetAt(R, t) { // the sirens' guide (cents) at context frame t; null outside a sing pass
    for (const s of R.segs) if (t >= s.a && t < s.b) { const u = (t - s.a) / (s.b - s.a), v = 0.5 - 0.5 * Math.cos(Math.PI * u); return { c: s.from + (s.to - s.from) * v, sing: s.sing }; }
    return null;
  }
  const prFold = (e) => { let o = 0; while (e > 600) { e -= 1200; o++; } while (e < -600) { e += 1200; o--; } return [e, o]; }; // another octave: the same note
  function prFrame(f) {
    const R = PR.run; if (!R || R.done || f.test) return;
    PR.last = f; R.frames.push(f); if (R.frames.length > 6000) R.frames.splice(0, 1000); // (a minute of frames: the sirens' trace, the tests)
    const SR = E.SR, voiced = f.cents != null && f.db > R.gateDb;
    if (R.kind === 'long' || R.kind === 'scale') {
      const st = R.steps.find((s) => f.t >= s.listenF && f.t < s.endF && !s.done); if (!st) return;
      // speaker: between the echo fit and "sing", the drone alone is left in the cleaned signal: what stays of it sets
      // this note's floor (+6 dB), so its remains can never count as singing (capped: a voice sung early still counts)
      if (f.t < st.singF) { if (R.mode === 'speaker' && R.gateFrom > st.listenF && f.t > R.gateFrom + 0.05 * SR) { const g = Math.max(st.gate == null ? -55 : st.gate, f.db + 6); st.gate = Math.min(-38, g); if (g > -38) R.loudBleed = true; } return; } // (+50 ms: a window that started before the fit still holds the drone)
      const sv = f.cents != null && f.db > (st.gate == null ? R.gateDb : st.gate);
      st.n++; let inT = false;
      if (sv) { st.nV++; const [e, o] = prFold(f.cents - st.target); f.err = e; f.oct = o; inT = Math.abs(e) <= PR_GREEN; if (inT) st.nIn++; }
      const h = st.hold;
      if (inT) { if (h.s < 0 || f.t - h.l > PR_GRACE_S * SR) h.s = f.t; h.l = f.t; h.cur = (h.l - h.s + PR_HOP) / SR; h.best = Math.max(h.best, h.cur); }
      else if (h.s >= 0 && f.t - h.l > PR_GRACE_S * SR) { h.s = -1; h.cur = 0; }
      if (h.best >= st.need) { st.done = true; st.endedF = f.t; prAdvance(R, st); }
    } else if (R.kind === 'sirens') {
      const g = prTargetAt(R, f.t - R.latF); f.tgt = g && g.c;
      if (voiced && g && g.sing) { const [e] = prFold(f.cents - g.c); f.err = e; R.sing.push([f.t, f.cents]); }
    } else {
      const b = R.br;
      if (f.t < R.floorF) { b.floor.push(f.db); return; }
      if (b.floorDb == null) { const s = b.floor.slice().sort((x, y) => x - y); b.floorDb = s.length ? s[s.length >> 1] : -70; }
      const loud = f.db > b.floorDb + 10 && f.ap > 0.3; // noise, not a sung tone
      if (loud) { if (b.start < 0) b.start = f.t; b.last = f.t; b.dbs.push([f.t, f.db]); }
      if (b.start >= 0 && f.t - b.last > 0.7 * SR) prFinish();
      else if (b.start >= 0 && (b.last - b.start) / SR >= R.cfg.breath + 5) prFinish();
    }
  }
  function prAdvance(R, st) { // a note held long enough: the next one starts now (no waiting out its time)
    const i = R.steps.indexOf(st), SR = E.SR, now = prNow(), shift = st.endF - Math.max(now, st.endedF) - Math.round(0.1 * SR);
    if (shift <= 0) return;
    for (let k = i + 1; k < R.steps.length; k++) { const s = R.steps[k]; s.listenF -= shift; s.singF -= shift; s.endF -= shift; }
    st.endF -= shift; R.endF -= shift;
    prReplan(R, i + 1);
  }
  function prReplan(R, from) { // re-send the drone plan from step "from" on (the times moved)
    prDrone({ clearQ: true });
    const SR = E.SR, level = R.cfg.level;
    for (let k = from; k < R.steps.length; k++) { const s = R.steps[k], listen = (s.singF - s.listenF) / SR;
      prDrone({ at: s.listenF, drone: { hz: c2hz(s.target), level } });
      if (R.mode === 'speaker' && level > 0) prDrone({ at: s.listenF + Math.round(0.2 * SR), learn: Math.round((listen - 0.5) * SR) }); }
    prDrone({ at: R.endF, drone: { level: 0 } });
  }
  function prTick() { const R = PR.run; if (!R || R.done) return; if (prNow() >= R.endF + Math.round(0.3 * E.SR)) prFinish(); }
  function prScore(R) {
    const SR = E.SR, s = { id: R.id, at: R.at, kind: R.kind, mode: R.mode, oct: R.cfg.oct || 0, range: [R.plan.lo, R.plan.hi], measured: !!R.plan.r.measured, secs: Math.round((Date.now() - R.at) / 100) / 10, rec: !!(R.rec && R.rec.length) };
    if (R.kind === 'long' || R.kind === 'scale') {
      const used = R.steps.filter((x) => x.n > 0);
      s.notes = used.map((x) => ({ c: x.target, best: +x.hold.best.toFixed(2), need: x.need, inTune: x.n ? Math.round(100 * x.nIn / x.n) : 0, ok: x.hold.best >= x.need }));
      s.score = !used.length ? 0 : R.kind === 'long' ? Math.round(s.notes.reduce((a, x) => a + 100 * Math.min(1, x.best / x.need), 0) / R.steps.length) : Math.round(100 * s.notes.filter((x) => x.ok).length / R.steps.length);
      s.best = used.length ? Math.max(...s.notes.map((x) => x.best)) : 0;
      s.learn = R.learned.length ? +(R.learned.reduce((a, x) => a + x.reductionDb, 0) / R.learned.length).toFixed(1) : null;
    } else if (R.kind === 'sirens') { // the lag that fits best (0–400 ms: what he heard vs when he sang), then |error|
      let best = null;
      for (let lag = 0; lag <= 0.4 * SR; lag += 0.01 * SR) {
        let sum = 0, n = 0, in50 = 0;
        for (const [t, c] of R.sing) { const g = prTargetAt(R, t - lag); if (!g || !g.sing) continue; const e = Math.abs(prFold(c - g.c)[0]); sum += e; n++; if (e <= PR_YELLOW) in50++; }
        if (n >= 20 && (!best || sum / n < best.err)) best = { err: sum / n, lagMs: Math.round(lag / SR * 1000), n, in50: Math.round(100 * in50 / n) };
      }
      s.err = best ? Math.round(best.err) : null; s.lagMs = best ? best.lagMs : null; s.in50 = best ? best.in50 : 0; s.voicedSec = best ? +(best.n * PR_HOP / SR).toFixed(1) : 0;
      s.score = best ? Math.max(0, Math.round(100 - best.err)) : 0;
    } else {
      const b = R.br, dur = b.start >= 0 ? (b.last - b.start + PR_HOP) / SR : 0, mid = b.dbs.filter(([t]) => t >= b.start + 0.3 * SR && t <= b.last - 0.3 * SR).map((x) => x[1]);
      const mean = mid.length ? mid.reduce((a, x) => a + x, 0) / mid.length : 0, sd = mid.length > 3 ? Math.sqrt(mid.reduce((a, x) => a + (x - mean) * (x - mean), 0) / mid.length) : 0;
      const steady = Math.max(0.3, Math.min(1, 1 - (sd - 2) / 8));
      s.dur = +dur.toFixed(1); s.target = R.cfg.breath; s.sdDb = +sd.toFixed(1); s.floorDb = b.floorDb != null ? +b.floorDb.toFixed(1) : null;
      s.score = Math.round(100 * Math.min(1, dur / R.cfg.breath) * steady);
    }
    return s;
  }
  async function prFinish() {
    const R = PR.run; if (!R || R.done) return;
    R.done = true; clearInterval(R.timer);
    prDrone({ clearQ: true }); prDrone({ drone: { level: 0 } }); prDrone({ record: false });
    const s = prScore(R), heard = R.kind === 'breath' ? R.br.start >= 0 : R.kind === 'sirens' ? R.sing.length > 0 : R.steps.some((x) => x.nV > 0);
    if (R.rec && R.rec.length) { // ⏺: the session's own audio, kept on the phone
      const n = R.rec.reduce((a, x) => a + x.length, 0), pcm = new Int16Array(n); let o = 0;
      for (const x of R.rec) { for (let i = 0; i < x.length; i++) { const v = x[i]; pcm[o++] = v >= 1 ? 32767 : v <= -1 ? -32768 : Math.round(v * 32767); } }
      try { await REC.op('tchunks', 'readwrite', (st) => st.put(pcm, 'pr:audio:' + s.id)); s.audio = true; } catch (e) { s.audio = false; }
    }
    R.result = s;
    if (heard) { await prSave(s); ui.status('נשמר תרגול: ' + PR_KINDS[s.kind] + ' · ניקוד ' + s.score); }
    prUI(); prHist();
  }
  // ---- the screen
  function prOpen(kind, opt) {
    if (E.playing) pause(); if (REC.on) return;
    if (typeof vaHide === 'function' && !$('vaBox').hidden) vaHide();
    if (kind && PR_KINDS[kind]) PR.kind = kind;
    if (opt && Number.isFinite(opt.cents)) { const p = prPlan('long'); let k = 0; p.notes.forEach((c, i) => { if (Math.abs(c - opt.cents) < Math.abs(p.notes[k] - opt.cents)) k = i; }); PR.noteIdx = k; }
    $('prBox').hidden = false; document.body.classList.add('va-on');
    if (REC.asking) REC.askPlace(); // (a question left open when the screen closed: ▶️ still waits for it)
    prUI(); prHist(); prDraw(); if (typeof backSync === 'function') backSync();
  }
  async function prClose() {
    if (PR.run && !PR.run.done) await prFinish();
    PR.run = null; cancelAnimationFrame(PR.raf); PR.raf = 0;
    if (PR.node) { // the tone fades (30 ms), then the node ends: nothing of the practice runs while the screen is closed
      prDrone({ clearQ: true }); prDrone({ drone: { level: 0 } }); prDrone({ record: false });
      const n = PR.node, o = PR.out; PR.node = null; PR.out = null;
      setTimeout(() => { try { n.port.postMessage({ stop: true }); n.disconnect(); o.disconnect(); } catch (e) { /* gone */ } }, 300);
    }
    if (PR.src && PR.src !== window.__PR_SRC) { try { PR.src.disconnect(); } catch (e) { /* gone */ } PR.src = null; if (PR.mic) PR.mic.close(); }
    $('prBox').hidden = true; document.body.classList.remove('va-on');
    if (REC.asking) REC.askPlace();
    if (typeof backSync === 'function') backSync();
  }
  async function prGo() {
    if (PR.run && !PR.run.done) { await prFinish(); return; } // ⏹️ סיום
    $('prGo').disabled = true;
    try { if (!(await prAudio())) return; prStart(); } finally { $('prGo').disabled = false; }
    PR.raf = PR.raf || requestAnimationFrame(prDraw);
  }
  function prUI() {
    const R = PR.run, running = !!(R && !R.done), cfg = prCfg(), kind = PR.kind, r = prRange();
    document.querySelectorAll('#prTabs button').forEach((b) => { b.classList.toggle('on', b.dataset.kind === kind); b.setAttribute('aria-pressed', String(b.dataset.kind === kind)); b.disabled = running; });
    $('prHow').textContent = PR_HOW[kind];
    $('prGo').textContent = running ? '⏹️ סיום' : '▶️ התחלה';
    $('prRec').classList.toggle('on', !!PR.recOn); $('prRec').setAttribute('aria-pressed', String(!!PR.recOn)); $('prRec').disabled = running;
    $('prLvl').textContent = cfg.level > 0 ? '🔉 ' + Math.round(cfg.level * 100) + '%' : '🔇';
    const set = $('prSet'); set.replaceChildren();
    const chip = (txt, on, fn, lab) => { const b = el('button', 'chip' + (on ? ' on' : ''), txt); b.type = 'button'; if (lab) b.setAttribute('aria-label', lab); b.disabled = running; b.addEventListener('click', fn); return b; };
    if (kind === 'long') {
      const p = prPlan('long'); PR.noteIdx = Math.min(PR.noteIdx, p.notes.length - 1);
      set.append(chip('◀', false, () => { PR.noteIdx = Math.max(0, PR.noteIdx - 1); prUI(); }, 'צליל נמוך יותר'), el('span', 'pr-val', '⁦' + pName(p.notes[PR.noteIdx]) + '⁩'), chip('▶', false, () => { PR.noteIdx = Math.min(p.notes.length - 1, PR.noteIdx + 1); prUI(); }, 'צליל גבוה יותר'));
      [5, 10, 20].forEach((s) => set.append(chip(s + ' שנ׳', cfg.hold === s, () => { prSet({ hold: s }); prUI(); })));
    }
    if (kind === 'breath') [10, 20, 30].forEach((s) => set.append(chip(s + ' שנ׳', cfg.breath === s, () => { prSet({ breath: s }); prUI(); })));
    if (kind !== 'breath') set.append(chip('⬇️', false, () => { prSet({ oct: Math.max(-1, (cfg.oct || 0) - 1) }); prUI(); }, 'אוקטבה למטה'), el('span', 'pr-val', '⁦' + pName(m2c(prPlan(kind).lo)) + '–' + pName(m2c(prPlan(kind).hi)) + '⁩'), chip('⬆️', false, () => { prSet({ oct: Math.min(1, (cfg.oct || 0) + 1) }); prUI(); }, 'אוקטבה למעלה'));
    $('prRange').textContent = r.measured ? 'הטווח שלך (מההקלטות): ⁦' + pName(m2c(r.lo)) + '–' + pName(m2c(r.hi)) + '⁩' : 'עדיין אין הקלטות לניתוח: טווח אמצעי ⁦' + pName(m2c(r.lo)) + '–' + pName(m2c(r.hi)) + '⁩ (אפשר להזיז אוקטבה)';
    $('prMode').hidden = prMode() !== 'speaker'; $('prMode').textContent = '🔈 מצב רמקול: הצליל מנוכה מהמיקרופון, אבל עם אוזניות זה מדויק יותר.' + (PR.run && PR.run.loudBleed ? ' הצליל חזק מאוד ברמקול: כדאי להנמיך אותו (−).' : '');
    prStats();
  }
  function prStats() {
    const R = PR.run, f = PR.last; let note = '', cents = '', hold = '', score = '';
    if (R && (R.kind === 'long' || R.kind === 'scale')) {
      const st = R.steps.find((s) => !s.done && prNow() < s.endF) || R.steps[R.steps.length - 1], k = R.steps.indexOf(st) + 1;
      note = (prNow() < st.singF ? '🎵 להקשיב · ' : '🎤 לשיר · ') + '⁦' + pName(st.target) + '⁩ (' + k + '/' + R.steps.length + ')';
      hold = '⏱️ ' + (st.hold.cur || 0).toFixed(1) + ' / ' + st.need + ' שנ׳ · שיא ' + st.hold.best.toFixed(1);
    } else if (R && R.kind === 'sirens') { const g = prTargetAt(R, prNow()); note = g ? (g.sing ? '🎤 לשיר לפי הקו' : '🎵 להקשיב') : ''; }
    else if (R && R.kind === 'breath') { const b = R.br; note = prNow() < R.floorF ? '🤫 שקט רגע…' : b.start < 0 ? '🌬️ עכשיו: "ססס" ארוך' : '🌬️ ' + ((b.last - b.start) / E.SR).toFixed(1) + ' / ' + R.cfg.breath + ' שנ׳'; }
    if (f && f.err != null && R && !R.done) cents = '⁦' + (f.err > 0 ? '+' : f.err < 0 ? '−' : '') + Math.abs(Math.round(f.err)) + '⁩ סנט' + (f.oct ? ' (אוקטבה אחרת)' : '');
    else if (R && !R.done && R.kind !== 'breath') cents = '—';
    if (R && R.result) { const s = R.result; score = 'ניקוד: ' + s.score + (s.kind === 'sirens' && s.err != null ? ' · סטייה ממוצעת ' + s.err + ' סנט' : s.kind === 'breath' ? ' · ' + s.dur + ' שנ׳' : ''); }
    $('prNote').textContent = note; $('prCents').textContent = cents; $('prHold').textContent = hold; $('prScore').textContent = score;
  }
  function prDraw() {
    PR.raf = 0; const cv = $('prCv'); if (!cv || $('prBox').hidden) return;
    const dpr = window.devicePixelRatio || 1, W = Math.max(200, cv.clientWidth), Hh = 120; if (cv.width !== Math.round(W * dpr)) { cv.width = Math.round(W * dpr); cv.height = Math.round(Hh * dpr); }
    const g = cv.getContext('2d'); g.setTransform(dpr, 0, 0, dpr, 0, 0); g.clearRect(0, 0, W, Hh);
    const R = PR.run, f = PR.last, kind = R ? R.kind : PR.kind;
    if (kind === 'sirens' && R) { // time ->: the guide (white) and the voice (dots), 6 s back
      const now = prNow(), span = 6 * E.SR, lo = m2c(R.plan.lo) - 300, hi = m2c(R.plan.hi) + 300, y = (c) => Hh - 8 - (Hh - 16) * (c - lo) / (hi - lo), x = (t) => W * 0.85 + (t - now) / span * W * 0.85;
      g.strokeStyle = 'rgba(255,255,255,.8)'; g.lineWidth = 3; g.beginPath(); let first = true;
      for (let t = now - span; t <= now + 0.15 * span; t += E.SR / 25) { const tg = prTargetAt(R, t); if (!tg) { first = true; continue; } if (first) g.moveTo(x(t), y(tg.c)); else g.lineTo(x(t), y(tg.c)); first = false; }
      g.stroke();
      for (const q of R.frames) { if (q.cents == null || q.db <= R.gateDb || q.t < now - span) continue; const e = q.err; g.fillStyle = e == null ? 'rgba(170,170,200,.7)' : Math.abs(e) <= PR_GREEN ? '#4ade80' : Math.abs(e) <= PR_YELLOW ? '#facc15' : '#f87171'; g.beginPath(); g.arc(x(q.t - R.latF), y(q.cents + 1200 * (q.oct || 0)), 3, 0, 7); g.fill(); }
    } else if (kind === 'breath') { // the level (dB) with the room's floor
      const db = f ? f.db : -90, fl = R && R.br && R.br.floorDb != null ? R.br.floorDb : null, X = (d) => W * Math.max(0, Math.min(1, (d + 80) / 70));
      g.fillStyle = 'rgba(255,255,255,.12)'; g.fillRect(0, Hh / 2 - 18, W, 36);
      g.fillStyle = '#7fdccf'; g.fillRect(0, Hh / 2 - 18, X(db), 36);
      if (fl != null) { g.fillStyle = '#facc15'; g.fillRect(X(fl + 10) - 1, Hh / 2 - 26, 3, 52); }
    } else { // the needle: −100 … +100 cents (left = low, right = high), green ±25, yellow ±50
      const X = (c) => W / 2 + (W / 2 - 10) * Math.max(-100, Math.min(100, c)) / 100;
      g.fillStyle = 'rgba(248,113,113,.25)'; g.fillRect(0, 30, W, 60);
      g.fillStyle = 'rgba(250,204,21,.35)'; g.fillRect(X(-PR_YELLOW), 30, X(PR_YELLOW) - X(-PR_YELLOW), 60);
      g.fillStyle = 'rgba(74,222,128,.45)'; g.fillRect(X(-PR_GREEN), 30, X(PR_GREEN) - X(-PR_GREEN), 60);
      g.fillStyle = 'rgba(255,255,255,.7)'; g.font = '14px sans-serif'; g.textAlign = 'left'; g.fillText('נמוך', 6, 22); g.textAlign = 'right'; g.fillText('גבוה', W - 6, 22);
      if (f && f.err != null && R && !R.done) { const e = f.err; g.fillStyle = Math.abs(e) <= PR_GREEN ? '#4ade80' : Math.abs(e) <= PR_YELLOW ? '#facc15' : '#f87171'; g.fillRect(X(e) - 3, 22, 6, 76); }
    }
    if (R && f && f.at && !f.shown) { f.shown = performance.timeOrigin + performance.now(); R.paint.push({ lagMs: (PR.ctx.currentTime - f.end / E.SR) * 1000, workerToPaint: f.shown - f.at, centreMs: (PR.ctx.currentTime - f.t / E.SR) * 1000 }); if (R.paint.length > 2000) R.paint.shift(); } // (the latency gate: the window's last sample / its centre -> on screen)
    prStats();
    if (!$('prBox').hidden) PR.raf = requestAnimationFrame(prDraw);
  }
  async function prHist() {
    const box = $('prHist'); if (!box) return; const all = (await prSessions()).filter((s) => s.kind === PR.kind).slice(-20); box.replaceChildren();
    box.append(el('p', 'va-h', 'התקדמות: ' + PR_KINDS[PR.kind]));
    if (!all.length) { box.append(el('p', 'va-note', 'עוד אין תרגולים כאלה. אחרי כל תרגול יופיע כאן הניקוד.')); return; }
    const W = 320, Hh = 90, ns = 'http://www.w3.org/2000/svg', svg = document.createElementNS(ns, 'svg'); svg.setAttribute('viewBox', '0 0 ' + W + ' ' + Hh); svg.setAttribute('class', 'va-svg pr-chart'); svg.setAttribute('role', 'img');
    svg.setAttribute('aria-label', 'ניקוד ב-' + all.length + ' התרגולים האחרונים: ' + all.map((s) => s.score).join(', '));
    const x = (i) => 12 + (W - 24) * (all.length === 1 ? 0.5 : i / (all.length - 1)), y = (v) => Hh - 10 - (Hh - 20) * v / 100;
    const pl = document.createElementNS(ns, 'polyline'); pl.setAttribute('points', all.map((s, i) => x(i) + ',' + y(s.score)).join(' ')); pl.setAttribute('fill', 'none'); pl.setAttribute('stroke', '#7fdccf'); pl.setAttribute('stroke-width', '2.5'); svg.append(pl);
    all.forEach((s, i) => { const c = document.createElementNS(ns, 'circle'); c.setAttribute('cx', x(i)); c.setAttribute('cy', y(s.score)); c.setAttribute('r', '4'); c.setAttribute('fill', '#7fdccf'); svg.append(c); });
    box.append(svg);
    const last = all[all.length - 1], prev = all.length > 1 ? all[all.length - 2] : null;
    box.append(el('p', 'va-note', 'אחרון: ' + last.score + (prev ? ' (קודם: ' + prev.score + ')' : '') + ' · ' + new Date(last.at).toLocaleDateString('he-IL')));
    all.slice().reverse().filter((s) => s.audio).slice(0, 3).forEach((s) => { const b = el('button', 'chip', '▶️ ההקלטה מ-' + new Date(s.at).toLocaleTimeString('he-IL', { hour: '2-digit', minute: '2-digit' })); b.type = 'button'; b.addEventListener('click', () => prPlayRec(s.id)); box.append(b); });
  }
  async function prPlayRec(id) {
    const pcm = await REC.op('tchunks', 'readonly', (st) => st.get('pr:audio:' + id)); if (!pcm || !pcm.length) return;
    const c = prCtx(); await c.resume(); const b = c.createBuffer(1, pcm.length, E.SR), d = b.getChannelData(0); for (let i = 0; i < pcm.length; i++) d[i] = pcm[i] / 32768;
    const s = c.createBufferSource(); s.buffer = b; s.connect(c.destination); s.start();
  }
  function prInit() {
    if (!$('prBox') || PR.wired) return;
    PR.wired = true;
    ['prEntry', 'prEntry2', 'prEntry3'].forEach((id) => $(id).addEventListener('click', () => prOpen())); // (header, takes, the welcome card)
    $('prClose').addEventListener('click', () => prClose());
    $('prGo').addEventListener('click', prGo);
    $('prRec').addEventListener('click', () => { PR.recOn = !PR.recOn; prUI(); });
    $('prLvlDn').addEventListener('click', () => { const v = Math.max(0, Math.round((prCfg().level - 0.1) * 10) / 10); prSet({ level: v }); if (PR.run && !PR.run.done) { PR.run.cfg.level = v; prDrone({ drone: { level: v } }); } prUI(); });
    $('prLvlUp').addEventListener('click', () => { const v = Math.min(1, Math.round((prCfg().level + 0.1) * 10) / 10); prSet({ level: v }); if (PR.run && !PR.run.done) { PR.run.cfg.level = v; prDrone({ drone: { level: v } }); } prUI(); });
    const tabs = $('prTabs'); Object.entries(PR_KINDS).forEach(([k, n]) => { const b = el('button', 'chip', n); b.type = 'button'; b.dataset.kind = k; b.addEventListener('click', () => { PR.kind = k; prUI(); prHist(); prDraw(); }); tabs.append(b); });
    document.addEventListener('visibilitychange', () => { if (document.visibilityState === 'hidden' && PR.run && !PR.run.done) prFinish(); }); // leaving the app ends (and keeps) the session
  }

  // ================================================================ take comp 🎤 (v0.9.0)
  // Several takes of the same song (same key and tempo) -> for each line, the best version. The originals are never
  // touched: the result is a NEW take ("הרכבה (n)") rendered sample-exactly on the song timeline from the chosen pieces.
  // - Rows: the lyric rows (if pasted), else the song's own lines (phrases). Columns: the takes in the same key / tempo
  //   (the others are listed with the reason). Each cell = that take's v0.7.0 line score colour; a tap plays the line
  //   from that take (with the band, from 1 s before) and picks it. "✨ הכי טוב" picks the best score per line.
  // - Score order per line: colour (green > yellow > red > grey), then % in tune, then how much of the line the take
  //   covers (the longer one wins a tie), then the smaller mean deviation.
  // - Each piece comes from its take exactly as that take plays: its own alignment (nudge) and gain, its cleaned track
  //   when 🧹 is on (speaker takes), else the raw one; mixing cleaned and raw pieces asks first.
  // - Cuts: in the pause between two lines when there is one, else at the quietest point within ±150 ms of the line's
  //   start; always an equal-power crossfade of 30 ms (no click, no hole).
  // - Rendered chunk by chunk (memory stays small on any song length); the chunks are written first and the take
  //   record last, then the pack gets all of it in ONE save: a kill while rendering leaves no take at all (its stray
  //   chunks are swept later), a kill after it is saved like any take (the next start's reconcile).
  // - A comp plays, shares and is analysed like any take. Re-opening it preloads its choices; a new render is always a
  //   NEW comp (the old one stays until the user deletes it).
  const CP = { box: null, rows: [], cols: [], out: [], an: new Map(), pick: new Map(), base: null, prev: null, hear: null, rendering: null, armed: false, log: [] };
  const CP_XF_S = 0.03, CP_NEAR_S = 0.15, CP_GAP_S = 0.06, CP_HEAD_S = 0.5, CP_TAIL_S = 1.0, CP_EDGE_S = 0.01;
  const CP_COL_RANK = { green: 3, yellow: 2, red: 1, grey: 0 };
  function cpIsComp(t) { return !!(t && t.engine === 'comp'); } // (a declaration: the take list uses it from boot on)
  const cpSrcKey = (t) => (t.clean && !t.clean.error && t.cleanOn !== false ? t.id + ':c' : t.id); // as chunkBuf plays it
  const cpNud = (t) => Math.round((t.nudgeMs || 0) * E.SR / 1000);
  const cpGain = (t) => (t.norm === false ? 1 : t.gain || 1);
  function cpRows() { // the rows: { i, num, t0, t1 (the sung end), e (the row's end for the score) }
    let r = [];
    if (LY.lines.length && LY.rows) r = LY.rows.filter((x) => x.kind === 'line' && Number.isFinite(x.t0)).map((x) => ({ i: x.i, num: x.i + 1, t0: x.t0, t1: Number.isFinite(x.t1) ? x.t1 : x.c1, e: x.c1 != null ? x.c1 : x.t1 }));
    else if (HV.A) r = (HV.A.phrases || []).map((p, i) => ({ i, num: i + 1, t0: p.t0, t1: p.t1, e: p.t1 }));
    r = r.filter((x) => Number.isFinite(x.t0) && Number.isFinite(x.t1) && x.t1 > x.t0).sort((a, b) => a.t0 - b.t0);
    for (let k = 0; k + 1 < r.length; k++) { r[k].t1 = Math.min(r[k].t1, r[k + 1].t0); r[k].e = Math.min(r[k].e, r[k + 1].t0); }
    return r;
  }
  // the group: the key / tempo of the active take (of a comp's sources), else the most common one
  function cpGroup() {
    const t = REC.active;
    if (t) return { semi: t.transpose || 0, tempo: t.tempo || 1 };
    const n = new Map(); REC.takes.forEach((x) => { const k = (x.transpose || 0) + '/' + (x.tempo || 1); n.set(k, (n.get(k) || 0) + 1); });
    const best = [...n.entries()].sort((a, b) => b[1] - a[1])[0]; if (!best) return { semi: 0, tempo: 1 };
    const [s, tp] = best[0].split('/'); return { semi: +s, tempo: +tp };
  }
  function cpWhyNot(t, g) { // null = can be used
    if (cpIsComp(t)) return 'הרכבה (לא מקור)';
    if (t.sr !== E.SR) return 'קצב דגימה אחר';
    if ((t.transpose || 0) !== g.semi) return 'סולם אחר (' + REC.lr((t.transpose > 0 ? '+' : t.transpose < 0 ? '−' : '') + Math.abs(t.transpose || 0)) + ')';
    if (Math.abs((t.tempo || 1) - g.tempo) > 1e-6) return 'קצב אחר (' + REC.lr(Math.round((t.tempo || 1) * 100) + '%') + ')';
    if (t.hasRef && REC.cleaning === t.id) return 'בניקוי…';
    return null;
  }
  function cpCov(t, r) { // the part of the row's sung span this take holds (0..1)
    const n = cpNud(t), a = Math.max(r.t0 * E.SR, t.startF + n), b = Math.min(r.t1 * E.SR, t.endF + n);
    return Math.max(0, b - a) / Math.max(1, (r.t1 - r.t0) * E.SR);
  }
  function cpScore(t, r) { // { sc (combine), cov, key: [..] }
    const a = CP.an.get(t.id), cov = cpCov(t, r);
    const ls = a ? a.lines.filter((s) => { const m = (s.t0 + s.t1) / 2; return m >= r.t0 && m < r.e; }) : [];
    const sc = ls.length ? HVo().combine(ls) : null, col = sc ? sc.col : 'none';
    return { sc, cov, col, key: [col in CP_COL_RANK ? CP_COL_RANK[col] : -1, sc && sc.pIn != null ? sc.pIn : -1, Math.round(cov * 100), sc && sc.mAbs != null ? -sc.mAbs : -999] };
  }
  const cpBetter = (x, y) => { for (let k = 0; k < x.length; k++) if (x[k] !== y[k]) return x[k] > y[k]; return false; };
  const CP_MIN_COV = 0.5; // a take that holds less than half of a line can't be picked for it
  function cpAuto() {
    CP.pick = new Map();
    CP.rows.forEach((r) => { let best = null, bk = null;
      CP.cols.forEach((t) => { const s = cpScore(t, r); if (s.cov < CP_MIN_COV) return; if (!best || cpBetter(s.key, bk)) { best = t; bk = s.key; } });
      if (best) CP.pick.set(r.i, best.id); });
  }
  // the analyses the colours come from: stored ones if still valid, else analysed now (one after the other)
  async function cpAnalyses(onEach) {
    const H = HVo(); if (!H || !PV.ref || !HV.A) return;
    const S = vaSongHere(), base = await vaBase(S);
    for (const t of CP.cols) {
      let a = await vaLoad(E.song.id, t.id);
      if (!vaFresh(a, t, base)) { if (onEach) onEach(t, false); try { a = await vaAnalyse(t, S); } catch (e) { a = null; } }
      if (a) CP.an.set(t.id, a);
      if (onEach) onEach(t, true);
      if ($('cpBox').hidden) return;
    }
  }
  function cpOpen() {
    if (REC.on || REC.busy || !E.song) return;
    if (E.playing) pause();
    if (typeof vaHide === 'function' && !$('vaBox').hidden) vaHide();
    CP.prev = REC.active; CP.armed = false;
    const g = cpGroup(); CP.group = g; CP.rows = cpRows();
    CP.cols = REC.takes.filter((t) => !cpWhyNot(t, g)); CP.out = REC.takes.filter((t) => cpWhyNot(t, g)).map((t) => ({ t, why: cpWhyNot(t, g) }));
    CP.an = new Map();
    const src = cpIsComp(REC.active) && REC.active.comp ? REC.active : null; // re-edit: its own choices
    if (src) { CP.pick = new Map(); CP.of = src.id; (src.comp.rows || []).forEach((x) => { if (x.take && CP.cols.some((t) => t.id === x.take)) CP.pick.set(x.i, x.take); }); } else { CP.of = null; CP.pick = null; }
    $('cpBox').hidden = false; document.body.classList.add('va-on');
    cpUI(); if (typeof backSync === 'function') backSync();
    cpAnalyses((t, done) => { $('cpMsg').textContent = done ? '' : 'מנתח את „⁨' + t.name + '⁩”…'; if (done) cpUI(); })
      .then(() => { if (!CP.pick) cpAuto(); $('cpMsg').textContent = ''; cpUI(); });
  }
  function cpStopHear() { if (CP.hear) { clearInterval(CP.hear.t); CP.hear = null; if (E.playing) pause(); } }
  async function cpClose() {
    cpStopHear();
    $('cpBox').hidden = true; document.body.classList.remove('va-on');
    if (CP.prev !== undefined && REC.active !== CP.prev && REC.takes.includes(CP.prev) && !CP.keepActive) REC.setActive(CP.prev, false);
    CP.keepActive = false;
    if (typeof backSync === 'function') backSync();
  }
  function cpHear(r, t) { // the line from this take, with the band, from 1 s before; stops after the line
    cpStopHear();
    if (REC.active !== t) REC.setActive(t, false);
    if (LOOP.on) { const nm = loopName(); loopSet(undefined, undefined, false); ui.status('החזרה על ' + nm + ' כובתה'); }
    seek(Math.max(0, r.t0 - PRE_ROLL)); play();
    const end = r.t1 + 0.4; CP.hear = { r: r.i, take: t.id, t: setInterval(() => { if (!E.playing || posF() / E.SR >= end) cpStopHear(); }, 50) };
  }
  function cpUI() {
    const grid = $('cpGrid'), C0 = CP.cols;
    $('cpNote').textContent = C0.length < 2 ? 'צריך לפחות שתי הקלטות של השיר הזה באותו סולם ובאותו קצב.' : '';
    $('cpOut').replaceChildren(...CP.out.map((x) => el('p', 'va-note', '„⁨' + x.t.name + '⁩” לא נכללת: ' + x.why)));
    const head = el('div', 'cp-row cp-head'); head.append(el('span', 'cp-lab', 'שורה'));
    C0.forEach((t) => { const h = el('span', 'cp-th', (/(\d+)\s*$/.exec(t.name) || [null, t.name])[1]); h.title = t.name; head.append(h); });
    const rows = CP.rows.map((r) => {
      const row = el('div', 'cp-row'); row.append(el('span', 'cp-lab', String(r.num)));
      C0.forEach((t) => {
        const s = cpScore(t, r), on = CP.pick && CP.pick.get(r.i) === t.id, b = el('button', 'cp-cell sc-' + s.col + (on ? ' on' : ''), on ? '✓' : '');
        b.type = 'button'; b.dataset.row = r.i; b.dataset.take = t.id;
        b.setAttribute('aria-pressed', String(!!on));
        b.setAttribute('aria-label', 'שורה ' + r.num + ' מ„' + t.name + '”: ' + (s.cov < CP_MIN_COV ? 'לא הוקלטה' : s.sc ? vaNumbers(s.sc, r.num) : 'אין ציון'));
        if (s.cov < CP_MIN_COV) { b.disabled = true; b.textContent = '—'; }
        else b.addEventListener('click', () => { if (!CP.pick) CP.pick = new Map(); CP.pick.set(r.i, t.id); CP.armed = false; cpUI(); cpHear(r, t); });
        row.append(b);
      });
      return row;
    });
    grid.style.setProperty('--cp-n', String(Math.max(1, C0.length)));
    grid.replaceChildren(head, ...rows);
    const n = CP.pick ? CP.pick.size : 0, mixed = cpMixed();
    $('cpSum').textContent = n ? n + ' מתוך ' + CP.rows.length + ' שורות נבחרו' + (CP.of ? ' (עריכה של הרכבה קיימת: התוצאה תהיה הרכבה חדשה)' : '') : '';
    $('cpWarn').hidden = !(mixed && CP.armed); $('cpWarn').textContent = 'חלק מהשורות נבחרו מהקלטות נקיות (🧹) וחלק מהקלטות לא נקיות: הצליל ישתנה בין השורות. לגעת שוב ב„יצירה” כדי להמשיך בכל זאת.';
    $('cpGo').disabled = !n || !!CP.rendering; $('cpAuto').disabled = C0.length < 1 || !!CP.rendering;
    $('cpGo').textContent = CP.rendering ? 'יוצר…' : CP.armed ? '✅ ליצור בכל זאת' : '✅ ליצור הרכבה';
  }
  function cpMixed() { if (!CP.pick) return false; const k = new Set(); for (const id of CP.pick.values()) { const t = REC.takes.find((x) => x.id === id); if (t) k.add(cpSrcKey(t) === t.id ? 'a' : 'c'); } return k.size > 1; }
  // ---- the render
  function cpReader(t) { // a take's samples on the song timeline, as it plays (its alignment, its gain), cached by chunk
    const key = cpSrcKey(t), n = cpNud(t), g = cpGain(t), C = E.Lf, cache = new Map();
    const get = async (k) => { if (cache.has(k)) return cache.get(k); const d = (await REC.getChunk(key, k)) || null; cache.set(k, d); if (cache.size > 3) cache.delete(cache.keys().next().value); return d; };
    return { t, key, g, async block(f0, len) { // Float32 (gain applied) of song frames [f0, f0 + len)
      const out = new Float32Array(len), lo = t.startF, hi = t.endF;
      for (let i = 0; i < len;) { const s = f0 + i - n, k = Math.floor(s / C), base = k * C, m = Math.min(len - i, base + C - s);
        if (s + m > lo && s < hi) { const d = await get(k); if (d) for (let j = 0; j < m; j++) { const q = s + j; if (q >= lo && q < hi) out[i + j] = d[q - base] * g / 32768; } }
        i += m; }
      return out; } };
  }
  async function cpQuietest(ra, rb, lo, hi, prefer) { // the frame in [lo, hi] where both pieces together are quietest
    const W = Math.round(0.01 * E.SR), step = Math.round(0.0025 * E.SR), a = lo - W, len = hi - lo + 2 * W;
    const x = ra ? await ra.block(a, len) : null, y = rb ? await rb.block(a, len) : null;
    const e = new Float64Array(len + 1); for (let i = 0; i < len; i++) { const v = (x ? x[i] * x[i] : 0) + (y ? y[i] * y[i] : 0); e[i + 1] = e[i] + v; }
    let best = prefer, bv = Infinity;
    for (let f = lo; f <= hi; f += step) { const i = f - a, v = e[Math.min(len, i + W)] - e[Math.max(0, i - W)];
      if (v < bv - 1e-12 || (Math.abs(v - bv) <= 1e-12 && Math.abs(f - prefer) < Math.abs(best - prefer))) { bv = v; best = f; } }
    return best;
  }
  async function cpPlan() { // the pieces: [{ t (or null = silence), a, b }] with the cuts between them, on song frames
    const SR = E.SR, R = CP.rows, pick = CP.pick || new Map(), byId = (id) => REC.takes.find((x) => x.id === id) || null;
    const ch = R.map((r) => ({ r, t: pick.has(r.i) ? byId(pick.get(r.i)) : null }));
    let f0 = ch.findIndex((x) => x.t), f1 = ch.length - 1; while (f1 >= 0 && !ch[f1].t) f1--;
    if (f0 < 0) return null;
    const use = ch.slice(f0, f1 + 1), readers = new Map(), rd = (t) => { if (!t) return null; if (!readers.has(t.id)) readers.set(t.id, cpReader(t)); return readers.get(t.id); };
    const first = use[0], last = use[use.length - 1];
    let S = Math.max(0, Math.round((first.r.t0 - CP_HEAD_S) * SR), first.t.startF + cpNud(first.t));
    let Z = Math.min(E.durF, Math.round((last.r.t1 + CP_TAIL_S) * SR), last.t.endF + cpNud(last.t));
    const pieces = [{ t: use[0].t, a: S, b: Z, rows: [use[0].r.i] }], cuts = [];
    for (let k = 1; k < use.length; k++) {
      const p = pieces[pieces.length - 1], cur = use[k];
      if ((cur.t && cur.t.id) === (p.t && p.t.id)) { p.rows.push(cur.r.i); continue; }
      const A = use[k - 1].r, B = cur.r, gap = B.t0 - A.t1, h = Math.round(CP_XF_S * SR / 2);
      let lo, hi, prefer, kind;
      if (gap >= CP_GAP_S) { lo = Math.round(A.t1 * SR) + h; hi = Math.round(B.t0 * SR) - h; prefer = Math.round((A.t1 + B.t0) / 2 * SR); kind = 'gap'; }
      else { lo = Math.round(Math.max(B.t0 - CP_NEAR_S, A.t0 + 0.05) * SR); hi = Math.round(Math.min(B.t0 + CP_NEAR_S, B.t1 - 0.05) * SR); prefer = Math.round(B.t0 * SR); kind = 'near'; }
      if (hi < lo) { lo = hi = Math.round(B.t0 * SR); }
      const at = await cpQuietest(rd(p.t), rd(cur.t), lo, hi, Math.min(hi, Math.max(lo, prefer)));
      p.b = at; cuts.push({ atF: at, kind, from: p.t ? p.t.id : null, to: cur.t ? cur.t.id : null });
      pieces.push({ t: cur.t, a: at, b: Z, rows: [cur.r.i] });
    }
    return { S, Z, pieces, cuts, rd };
  }
  async function cpRender() {
    if (CP.rendering || REC.on || REC.busy || !E.song) return;
    if (cpMixed() && !CP.armed) { CP.armed = true; cpUI(); return; }
    cpStopHear();
    const song = E.song.id, SR = E.SR, C = E.Lf;
    const id = 'm' + Date.now().toString(36) + Math.random().toString(36).slice(2, 6);
    CP.rendering = id; cpUI(); const t0 = performance.now();
    try {
      const P = await cpPlan(); if (!P) return;
      const need = (P.Z - P.S) * 2, fb = freeBytes();
      if (fb >= 0 && fb < need + SAVE_MARGIN_BYTES + FREE_REC_MIN_BYTES) { ui.status('אין מספיק מקום פנוי כדי ליצור הרכבה.'); spaceCheck('take'); return; }
      const used = [...new Set(P.pieces.filter((p) => p.t).map((p) => p.t))], G = Math.max(...used.map(cpGain)), h = Math.round(CP_XF_S * SR / 2), fe = Math.round(CP_EDGE_S * SR);
      const st = REC.newStats(); let clips = 0;
      const wIn = (f, a) => Math.sin(Math.PI / 2 * Math.min(1, Math.max(0, (f - (a - h)) / (2 * h)))), wOut = (f, b) => Math.cos(Math.PI / 2 * Math.min(1, Math.max(0, (f - (b - h)) / (2 * h))));
      const keys = [], k0 = Math.floor(P.S / C), k1 = Math.floor((P.Z - 1) / C);
      for (let k = k0; k <= k1; k++) {
        const fa = Math.max(P.S, k * C), fz = Math.min(P.Z, (k + 1) * C), acc = new Float32Array(fz - fa);
        for (let j = 0; j < P.pieces.length; j++) {
          const p = P.pieces[j]; if (!p.t) continue;
          const hasPrev = j > 0, hasNext = j < P.pieces.length - 1, xa = hasPrev ? p.a - h : p.a, xb = hasNext ? p.b + h : p.b;
          const a = Math.max(fa, xa), b = Math.min(fz, xb); if (b <= a) continue;
          const x = await P.rd(p.t).block(a, b - a);
          for (let f = a; f < b; f++) { let w = 1;
            if (hasPrev && f < p.a + h) w *= wIn(f, p.a); else if (!hasPrev && f < P.S + fe) w *= Math.sin(Math.PI / 2 * (f - P.S) / fe);
            if (hasNext && f >= p.b - h) w *= wOut(f, p.b); else if (!hasNext && f >= P.Z - fe) w *= Math.sin(Math.PI / 2 * Math.max(0, P.Z - 1 - f) / fe);
            acc[f - fa] += w * x[f - a]; }
        }
        const d = new Int16Array(C);
        for (let i = 0; i < acc.length; i++) { const v = acc[i] / G; REC.acc(st, v); if (v >= 0.99 || v <= -0.99) clips++; d[fa - k * C + i] = v >= 1 ? 32767 : v <= -1 ? -32768 : Math.round(v * 32767); }
        await REC.op('tchunks', 'readwrite', (s) => s.put(d, id + ':' + k)); keys.push(id + ':' + k); // (no pack mark yet: see below)
        $('cpMsg').textContent = 'יוצר הרכבה… ' + Math.round(100 * (k - k0 + 1) / (k1 - k0 + 1)) + '%';
        if (CP.onChunk) CP.onChunk(k - k0, k1 - k0 + 1); // (tests: the memory per chunk)
        await new Promise((r) => setTimeout(r, 0));
      }
      const lv = REC.levels(st), n = REC.takes.filter(cpIsComp).length + 1, all = new Set(used.map((x) => x.id));
      const spk = used.some((x) => x.mode === 'speaker'), est = used.some((x) => (x.latSource || (x.calibrated ? 'calibration' : 'estimate')) === 'estimate');
      const t = { id, songId: song, name: 'הרכבה (' + n + ')', created: Date.now(), sr: SR, startF: P.S, endF: P.Z, transpose: CP.group.semi, tempo: CP.group.tempo,
        engine: 'comp', engineReason: 'comp', mode: spk ? 'speaker' : 'headphones', latencyF: 0, calibrated: used.every((x) => x.calibrated || x.latSource === 'count-in'), latSource: est ? 'estimate' : 'comp',
        nudgeMs: 0, gain: +G.toFixed(4), norm: true, samples: P.Z - P.S, level: { peakDb: REC.db(lv.peak), rmsDb: REC.db(lv.rms), loudDb: REC.db(lv.loud), clips, clipSamples: 0 },
        shiftLatF: used[0].shiftLatF || 0,
        comp: { v: 1, of: CP.of || null, mixed: cpMixed(), xfMs: CP_XF_S * 1000, ms: Math.round(performance.now() - t0),
          sources: used.map((x) => ({ id: x.id, name: x.name, src: cpSrcKey(x) === x.id ? 'raw' : 'clean', nudgeMs: x.nudgeMs || 0, gain: cpGain(x) })),
          rows: CP.rows.map((r) => ({ i: r.i, num: r.num, take: CP.pick && CP.pick.get(r.i) && all.has(CP.pick.get(r.i)) ? CP.pick.get(r.i) : null })),
          pieces: P.pieces.map((p) => ({ take: p.t ? p.t.id : null, fromF: p.a, toF: p.b, rows: p.rows })), cuts: P.cuts } };
      await REC.op('takes', 'readwrite', (s) => s.put(t)); // the record goes last: before it, nothing of this take exists
      keys.forEach((key) => PK.mark(song, { take: id, key })); // and the pack gets the record + every chunk in one save
      if (PKS) { clearTimeout(PK.t); PK.flush(); }
      CP.rendering = null; // (rendered and saved; what follows is the usual new-take path)
      CP.log.push({ id, at: Date.now(), ms: t.comp.ms, chunks: keys.length, sec: +((P.Z - P.S) / SR).toFixed(2) }); if (CP.log.length > 20) CP.log.shift();
      if (E.song && E.song.id === song) { REC.takes.push(t); PK.afterTake(t); CP.keepActive = true; REC.setActive(t, true); }
      ui.status('נשמרה "' + t.name + '" (' + t.comp.rows.filter((x) => x.take).length + ' שורות מ-' + used.length + ' הקלטות). ההקלטות המקוריות לא השתנו.');
      CP.last = t;
      if (!$('cpBox').hidden) cpClose();
    } catch (e) { ui.status('יצירת ההרכבה נכשלה'); CP.err = String(e && e.stack || e); }
    finally { CP.rendering = null; CP.armed = false; $('cpMsg').textContent = ''; if (!$('cpBox').hidden) cpUI(); }
  }
  // chunks of a comp that never got its record (the app was killed while rendering): removed
  async function cpSweep() {
    try {
      const keys = (await REC.op('tchunks', 'readonly', (s) => s.getAllKeys(IDBKeyRange.bound('m', 'm￿')))) || [];
      if (!keys.length) return 0;
      const ids = new Set(((await REC.op('takes', 'readonly', (s) => s.getAllKeys())) || []).map(String));
      const stray = keys.map(String).filter((k) => { const tid = k.split(':')[0]; return !ids.has(tid) && tid !== CP.rendering; });
      for (const k of stray) await REC.op('tchunks', 'readwrite', (s) => s.delete(k));
      CP.swept = (CP.swept || 0) + stray.length; return stray.length;
    } catch (e) { return 0; }
  }
  function cpInit() {
    if (!$('cpBox')) return;
    $('cpOpen').addEventListener('click', () => cpOpen());
    $('cpClose').addEventListener('click', () => cpClose());
    $('cpAuto').addEventListener('click', () => { cpAuto(); CP.armed = false; cpUI(); });
    $('cpGo').addEventListener('click', () => cpRender());
    setTimeout(cpSweep, 4000);
  }

  // ---- (v0.7.2) Android back: closes the top-most open thing first — a confirm dialog (its non-destructive answer), the
  // voice report, the lyric editor (never with unsaved text: it says so and stays), a lyric line's bar, the song
  // library. The page tells the app whether anything is open (Android.setBack), so with nothing open back keeps the
  // system behaviour (leave / minimise; the settings are saved as the app leaves).
  const backOpen = () => !$('delBox').hidden || !$('tkBox').hidden || !$('cpBox').hidden || !$('prBox').hidden || !$('vaBox').hidden || !$('songBox').hidden || !$('lyrEditor').hidden || !!document.querySelector('.lyr-act') || !$('lib').hidden;
  function harmonyBack() {
    let r = true;
    if (!$('delBox').hidden) $('delNo').click();
    else if (!$('tkBox').hidden) $('tkNo').click();
    else if (!$('cpBox').hidden) cpClose(); // (v0.9.0) the take comp screen (a render in progress goes on)
    else if (!$('prBox').hidden) prClose(); // (v0.8.0) the practice screen: its tone stops, the session is kept
    else if (!$('vaBox').hidden) vaHide();
    else if (!$('songBox').hidden) songClose(); // (v0.9.1) the song search sheet
    else if (!$('lyrEditor').hidden) { if ($('lyrText').value.replace(/\r\n?/g, '\n') !== LY.text) ui.status('יש במילים שינויים שלא נשמרו: „שמירה” או „ביטול”'); else $('lyrCancel').click(); }
    else if (document.querySelector('.lyr-act')) document.querySelectorAll('.lyr-act').forEach((x) => x.remove());
    else if (!$('lib').hidden) $('libBtn').click();
    else r = false;
    backSync(); return r;
  }
  let backLast = null;
  function backSync() { const o = backOpen(); if (o === backLast) return; backLast = o; try { if (ANDROID && window.Android.setBack) window.Android.setBack(o); } catch (e) { /* older bridge */ } }
  window.harmonyBack = harmonyBack;
  document.addEventListener('click', () => setTimeout(backSync, 0), true); setInterval(backSync, 700); // (taps open / close them; the timer catches the rest)
  window.harmonyControl = { play: () => play(), pause: () => pause(), toggle: () => (E.playing ? pause() : play()), isPlaying: () => E.playing,
    background: (b) => { E.bg = !!b; idleCheck(); if (b && PKS) { clearTimeout(PK.t); PK.flush(); } } }; // (v0.7.2) leaving the app: save now, not 2 s later
  // test / diagnostics hook (read-mostly)
  window.__harmony = {
    E, mix, play, pause, seek, stopToStart, lyJump, lyFine, CP, cpOpen, cpClose, cpRender, cpAuto, cpRows, cpScore, cpPlan, cpSweep, cpSrcKey, PR, prOpen, prClose, prGo, prAudio, prPlan, prRange, prSessions, prScore, prTargetAt, doMix, LOOP, loopSet, setSemi, PK, VA, vaUpdate, vaOpen, vaRender, vaExercise, vaTone, vaBase, vaAnalyse, vaAnalyseOther, vaAllData, vaRows, vaFirstNote, vaPractise, vaSrc, spaceCheck, LIMITS: { PACK_WARN_BYTES, FREE_WARN_BYTES, FREE_REC_MIN_BYTES, SAVE_MARGIN_BYTES }, openSong, skip, skipStarts, musicDir, REC, ui, fxBuild, FX_DEF, rvGain, AS, asSet, PV, pvSet, pvUpdate, posSec: () => posF() / E.SR, TP, TIER, HV, audibleSec, LY, mapLines, setTempo, stretchLatF, release, idleCheck,
    stats: () => ({ sr: E.SR, D: E.D, calPeak: E.calPeak, liveChunks: [...E.chunks.keys()], bytes: E.bytes, peakBytes: E.peakBytes,
      decodes: E.decodes, lateJoins: E.lateJoins, errors: E.errors, sources: E.run ? E.run.sources.size : 0, makeup: E.makeup || null,
      state: E.ctx && E.ctx.state, playing: E.playing, bootError: E.bootError || null, released: E.released, releases: E.releases }),
  };
  boot();
})();
