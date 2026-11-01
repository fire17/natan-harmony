/* Harmony voice analysis (v0.7.0): what the take's own voice did, against the song's own vocal melody.
   ON THE PHONE ONLY: runs in the pitch Worker (and as a Node module for the tests); the voice never leaves the phone.
   Input = the take's pitch + level track (pitch.js, 10 ms song frames), the song's melody.json (shifted to the key the
   take was sung in), the song's lines (analysis.json phrases: referred to by NUMBER and time, never by text), the
   beats, and the take's metadata (nudge, transpose, latency source, mode).
   Output (JSON, small, derived and recomputable): per-line scores, per-take measures, a note histogram for the range,
   and the song's melody histogram for a key suggestion. aggregate() combines many takes (all songs); findings() turns
   measures into ranked findings with exercises (EX, Hebrew, rule-based). Every threshold is a named constant (K). */
(function (root) {
  const P = (typeof module !== 'undefined' && module.exports && typeof require === 'function') ? require('./pitch.js') : root.HarmonyPitch;
  const VOICE_V = 1; // analysis.json format / method version (a newer method re-analyses)

  // ---- named constants (cents, ms, s, dB, fractions). Frame = 10 ms.
  const K = Object.freeze({
    IN_TUNE_C: 50,          // a frame "in tune": within ±50 cents of the melody (octave-tolerant)
    LINE_COVER_MIN: 0.3,    // voiced take frames / confident melody frames of a line below this: not sung (grey, not red)
    LINE_MIN_FRAMES: 15,    // fewer comparable frames: no score (grey)
    LINE_GREEN_IN: 70,      // green: >= 70 % of the line in tune …
    LINE_GREEN_MED: 35,     // … and its median deviation within ±35 cents
    LINE_YELLOW_IN: 45,     // yellow: >= 45 % in tune; below: red
    STABLE_C: 30,           // a melody frame is "steady" when the melody stays within ±30 cents over ±50 ms
    RUN_MIN_MS: 100,        // melody runs shorter than 100 ms (confident blips) do not start / end a line
    BIAS_WIN_C: 150,        // deviations beyond ±150 cents (a wrong note, not a tendency) are left out of the bias
    BIAS_FLAG_C: 15,        // overall flat / sharp worth telling: |mean| >= 15 cents
    REG_BIAS_FLAG_C: 25,    // a register (third of his range) flat / sharp: |mean| >= 25 cents …
    REG_MIN_FRAMES: 150,    // … over at least 1.5 s of sung frames in it
    REG_SPREAD_C: 25,       // registers differ by >= 25 cents: told per register, not as one overall tendency
    HELD_MIN_MS: 400,       // a held note: the melody stays within ±HELD_REF_TOL_C for >= 400 ms
    HELD_REF_TOL_C: 40,
    HELD_EDGE_MS: 100,      // the note's first 100 ms (the entry) are not part of its sustain
    HELD_END_MS: 150,       // the "end of note" = its last 150 ms (minus HELD_TAIL_MS)
    HELD_TAIL_MS: 20,
    HELD_VOICED_MIN: 0.7,   // a held note counts only when >= 70 % of it is voiced in the take
    JITTER_FLAG_C: 20,      // unstable sustain: his pitch wobbles >= 20 cents (std around the note's own line) …
    JITTER_OVER_REF_C: 8,   // … and >= 8 cents more than the original singer's on the same notes
    END_DROP_FLAG_C: 25,    // note ends sag: the last 150 ms >= 25 cents lower (vs the melody) than the note's middle
    ONSET_GAP_MS: 60,       // a note entry: the melody silent >= 60 ms before it …
    ONSET_NOTE_MS: 150,     // … and then a note of >= 150 ms
    ONSET_MATCH_MS: 150,    // his entry = the start of a voiced run within ±150 ms of the melody's
    OVER_BASE_PCT: 15,      // a rate (scoops, cut / fading endings) counts only >= 15 points above the original singer's
    SCOOP_C: 70,            // a scoop: the note starts >= 70 cents below its target …
    SCOOP_MS: 60,           // … and takes >= 60 ms to come within SCOOP_REACH_C of it
    SCOOP_REACH_C: 30,
    SCOOP_LOOK_MS: 60,      // the start depth is read over the first 60 ms
    SCOOP_WIN_MS: 300,      // gives up after 300 ms (never reached: not a scoop, a wrong note)
    CLEAN_ENTRY_MS: 30,     // a clean entry: within SCOOP_REACH_C in <= 30 ms
    SCOOP_RATE_FLAG: 0.25,  // scoops worth telling: >= 25 % of entries
    TIMING_FLAG_MS: 25,     // early / late worth telling: |mean| >= 25 ms …
    TIMING_CONSIST: 0.6,    // … with >= 60 % of entries on that side
    BEAT_NEAR_MS: 70,       // an entry "on the beat": the melody's entry within ±70 ms of a beat
    RANGE_MIN_FRAMES: 30,   // a note counts for the range when sung >= 0.3 s in total …
    RANGE_IN_TUNE: 0.6,     // … and >= 60 % of that in tune
    RANGE_FIT_GAIN: 0.08,   // a key change is suggested when it puts >= 8 % more of the melody in his range
    END_PART: 0.25,         // a line's ending = its last 25 % (300 ms .. 1 s)
    END_MIN_MS: 300,
    END_MAX_MS: 1000,
    END_FALL_DB_FLAG: 8,    // the ending >= 8 dB softer than the line's middle
    END_FALL_C_FLAG: 30,    // the ending >= 30 cents lower (vs the melody) than the middle
    END_COVER_MIN: 0.6,     // line endings are judged only on lines he sang >= 60 % of
    CUT_MS: 250,            // a cut ending: his voice stops >= 250 ms before the melody's line ends
    CUT_RATE_FLAG: 0.25,    // >= 25 % of sung lines cut / fading
    BREATH_GAP_MS: 250,     // a pause in the melody of >= 250 ms is a place to breathe
    BREATH_RUN_S: 3,        // a line with >= 3 s without such a pause that he cut / faded: "too long for one breath"?
    LONG_RUN_S: 6,          // >= 6 s without a pause: long for one breath for anyone
    // the original singer, measured the same way (no vocal stem: these, from the original vocals of the four songs, v0.7.0):
    // his entries read ~45 ms early vs the melody's (the take tracker hears a voice start sooner than the melody's tracker)
    BASE_DEFAULT: Object.freeze({ src: 'default', timing: -45, scoop: 12, cut: 0, fade: 35, sag: 0 }),
    CONF_N: Object.freeze({ frames: [1500, 6000], regFrames: [300, 1500], lines: [4, 12], held: [4, 12], onsets: [8, 25], takes: [2, 4] }), // [medium, high]
  });

  const HOP_MS = 10, f = (ms) => Math.round(ms / HOP_MS), NONE = NaN;
  const fold = P.fold, med = P.med;
  const mean = (a) => (a.length ? a.reduce((p, c) => p + c, 0) / a.length : NaN);
  const sd = (a) => { if (a.length < 2) return NaN; const m = mean(a); return Math.sqrt(a.reduce((p, c) => p + (c - m) * (c - m), 0) / (a.length - 1)); };
  const r1 = (x) => (Number.isFinite(x) ? Math.round(x * 10) / 10 : null), r0 = (x) => (Number.isFinite(x) ? Math.round(x) : null);
  const conf = (n, [m, h]) => (n >= h ? 2 : n >= m ? 1 : 0);
  const midiOf = (c) => 33 + c / 100; // cents above 55 Hz (A1 = MIDI 33)
  function detrendSd(y) { // std around the least-squares line (a slow glide is not a wobble)
    const n = y.length; if (n < 5) return NaN;
    let sx = 0, sy = 0, sxx = 0, sxy = 0; for (let i = 0; i < n; i++) { sx += i; sy += y[i]; sxx += i * i; sxy += i * y[i]; }
    const b = (n * sxy - sx * sy) / (n * sxx - sx * sx || 1), a = (sy - b * sx) / n; let s = 0;
    for (let i = 0; i < n; i++) { const e = y[i] - a - b * i; s += e * e; }
    return Math.sqrt(s / (n - 2));
  }
  // colour of a line from its numbers (the ONLY rule: the rows, the 🎯 badge and the report all call this)
  function lineColour(s) {
    if (!s || !s.rec) return 'none';
    if (!(s.cov >= K.LINE_COVER_MIN) || !(s.nP >= K.LINE_MIN_FRAMES)) return 'grey';
    if (s.pIn >= K.LINE_GREEN_IN && Math.abs(s.med) <= K.LINE_GREEN_MED) return 'green';
    if (s.pIn >= K.LINE_YELLOW_IN) return 'yellow';
    return 'red';
  }
  // several lines shown as one row (lyrics merge / split lines): counts add up; the median is the frame-weighted one
  function combine(ls) {
    const rec = ls.filter((s) => s && s.rec); if (!rec.length) return null;
    const sc = rec.filter((s) => s.nP > 0), nP = sc.reduce((p, s) => p + s.nP, 0), nRef = rec.reduce((p, s) => p + s.nRef, 0), nV = rec.reduce((p, s) => p + s.nV, 0);
    const out = { n: rec.map((s) => s.n), rec: true, nRef, nV, cov: nRef ? Math.min(1, nV / nRef) : 0, nP, nIn: sc.reduce((p, s) => p + s.nIn, 0) };
    out.pIn = nP ? Math.round(100 * out.nIn / nP) : null;
    out.med = nP ? Math.round(sc.reduce((p, s) => p + s.med * s.nP, 0) / nP) : null;
    out.mAbs = nP ? Math.round(sc.reduce((p, s) => p + s.mAbs * s.nP, 0) / nP) : null;
    const tm = rec.filter((s) => s.tim != null); out.tim = tm.length ? Math.round(mean(tm.map((s) => s.tim))) : null;
    out.col = lineColour(out);
    return out;
  }

  // ---- one take
  // inp: { take: { f0, cents: Float32Array (NaN unvoiced), db: Float32Array }, ref: { cents, conf, minConf } (in the take's
  //        key), phrases: [{ t0, t1 }], beats: [s], nudgeMs, meta: { takeId, songId, created, transpose, src, mode, latSource },
  //        base: the song's original singer through this same analysis (baseline()) — entries are timed against him }
  function analyse(inp) {
    const t0 = Date.now(), tk = inp.take, ref = inp.ref, phr = inp.phrases || [], beats = inp.beats || [], meta = inp.meta || {};
    const nf = Math.round((inp.nudgeMs || 0) / HOP_MS), tf0 = tk.f0 + nf, tn = tk.cents.length; // the nudge moves his voice on the song timeline
    const T = (s) => { const k = s - tf0; return k >= 0 && k < tn ? tk.cents[k] : NONE; };
    const Lv = (s) => { const k = s - tf0; return k >= 0 && k < tn && tk.db ? tk.db[k] : -120; };
    const R = (s) => (s >= 0 && s < ref.cents.length && ref.conf[s] >= ref.minConf ? ref.cents[s] : NONE);
    const ok = (x) => x === x; // not NaN
    const cmp = P.compare({ f0: tf0, cents: tk.cents }, ref, phr, { pairs: true });
    const tA = tf0, tB = tf0 + tn; // his take on the song timeline (frames)
    const lines = [], pairsAll = [], hist = {}, onsets = [], held = [], ends = [];
    let framesV = 0; for (let k = 0; k < tn; k++) if (ok(tk.cents[k])) framesV++;
    cmp.lines.forEach((c, li) => {
      const q = phr[li], r0f = Math.floor(q.t0 * 100), r1f = Math.floor(q.t1 * 100) + 1;
      const inTake = Math.min(r1f, tB) - Math.max(r0f, tA);
      const s = { n: li + 1, t0: q.t0, t1: q.t1, rec: inTake >= 0.5 * (r1f - r0f) };
      lines.push(s); if (!s.rec) return;
      let nRef = 0, nV = 0;
      for (let x = r0f; x < r1f; x++) if (ok(R(x))) { nRef++; let v = false; for (let d = -30; d <= 30 && !v; d += 3) v = ok(T(x + d)); if (v) nV++; }
      Object.assign(s, { nRef, nV, cov: nRef ? Math.round(100 * Math.min(1, nV / nRef)) / 100 : 0, nP: 0, nIn: 0, pIn: null, med: null, mAbs: null, tim: null, lag: null });
      if (c.ok && c.pairs) {
        const ds = [];
        for (const [x, y] of c.pairs) { const d = fold(T(y) - R(x)); if (ok(d)) ds.push(d); }
        s.nP = ds.length; s.nIn = ds.filter((d) => Math.abs(d) <= K.IN_TUNE_C).length;
        s.pIn = ds.length ? Math.round(100 * s.nIn / ds.length) : null; s.med = r0(med(ds)); s.mAbs = r0(mean(ds.map(Math.abs))); s.lag = c.lagMs;
      }
      s.col = lineColour(s);
      if (s.col === 'grey' || s.col === 'none') return;
      const L = f(s.lag || 0); // the line's own timing (DTW): his voice at frame x + L sings the melody's frame x
      // the tendency (bias, range): his voice at x + L vs the melody at x, only where the melody holds still (±STABLE_C over
      // ±50 ms) — DTW pairs would pull every deviation toward the nearest melody value and hide a steady offset
      for (let x = r0f; x < r1f; x++) {
        const rv = R(x); if (!ok(rv)) continue;
        let st = true; for (const k of [-5, -3, 3, 5]) { const q = R(x + k); if (!ok(q) || Math.abs(q - rv) > K.STABLE_C) { st = false; break; } }
        if (!st) continue; const v = T(x + L); if (!ok(v)) continue;
        pairsAll.push([x, x + L, fold(v - rv)]);
      }

      // held notes: runs of the melody within ±HELD_REF_TOL_C of their running mean, >= HELD_MIN_MS
      let x = r0f;
      while (x < r1f) {
        if (!ok(R(x))) { x++; continue; }
        let y = x, sum = 0, cnt = 0;
        while (y < r1f && ok(R(y)) && (cnt === 0 || Math.abs(R(y) - sum / cnt) <= K.HELD_REF_TOL_C)) { sum += R(y); cnt++; y++; }
        if ((y - x) * HOP_MS >= K.HELD_MIN_MS) {
          const a = x + f(K.HELD_EDGE_MS), e1 = y - f(K.HELD_TAIL_MS), e0 = e1 - f(K.HELD_END_MS);
          const body = [], bodyRef = [], xd = [], endD = []; let voiced = 0, all = 0;
          for (let z = a; z < e1; z++) { all++; const v = T(z + L); if (!ok(v)) continue; voiced++; const d = fold(v - R(z)); if (Math.abs(d) > K.BIAS_WIN_C) continue;
            if (z < e0) { body.push(v); bodyRef.push(R(z)); xd.push(d); } else endD.push(d); }
          if (all && voiced / all >= K.HELD_VOICED_MIN && body.length >= 10) {
            // octave-consistent: his pitch unwrapped to the melody's octave, so a fold never makes a fake wobble
            const base = med(body.map((v, i) => v - bodyRef[i])), un = body.map((v, i) => bodyRef[i] + fold(v - bodyRef[i] - base) + base);
            held.push({ line: s.n, jit: detrendSd(un), refJit: detrendSd(bodyRef), drop: endD.length >= 5 ? med(endD) - med(xd) : NaN });
          }
        }
        x = y;
      }
      // note entries: the melody silent >= ONSET_GAP_MS, then a note >= ONSET_NOTE_MS (its target = its median)
      for (let z = r0f; z < r1f; z++) {
        if (!ok(R(z))) continue;
        let len = 0; while (ok(R(z + len))) len++; // z starts a voiced run of the melody (runs are skipped whole)
        let gap = 0; while (gap < f(K.ONSET_GAP_MS) && z - 1 - gap >= 0 && !ok(R(z - 1 - gap))) gap++;
        if (gap >= f(K.ONSET_GAP_MS) && len * HOP_MS >= K.ONSET_NOTE_MS) {
          const tg = []; for (let k = f(50); k < Math.min(len, f(250)); k++) tg.push(R(z + k));
          onsets.push({ line: s.n, x: z, target: med(tg) });
        }
        z += len - 1;
      }
      // the line's ending: where his voice stops vs where the melody's does; level / pitch of the last part vs the middle
      let rf = -1, rl = -1;
      for (let z = r0f; z < r1f; z++) { if (!ok(R(z))) continue; let e = z; while (e < r1f && ok(R(e))) e++; if (e - z >= f(K.RUN_MIN_MS)) { if (rf < 0) rf = z; rl = e - 1; } z = e; }
      if (rf >= 0 && rl - rf >= f(600) && s.cov >= K.END_COVER_MIN) {
        // his last voiced frame of the runs that START before the melody's line ends (a run starting after it is the next line)
        let hl = -1; for (let z = rf + L, zs = -1; z <= Math.min(rl + L + 30, tB - 1); z++) { if (!ok(T(z))) { zs = -1; continue; } if (zs < 0) zs = z; if (zs <= rl + L) hl = z; }
        const span = rl - rf + 1, ep = Math.max(f(K.END_MIN_MS), Math.min(f(K.END_MAX_MS), Math.round(span * K.END_PART)));
        const m0 = rf + Math.round(span * 0.25), m1 = rf + Math.round(span * 0.75), e0 = rl + 1 - ep;
        const lvM = [], lvE = [], dM = [], dE = [];
        for (let z = m0; z < m1; z++) if (ok(R(z))) { lvM.push(Lv(z + L)); const d = fold(T(z + L) - R(z)); if (ok(d) && Math.abs(d) <= K.BIAS_WIN_C) dM.push(d); }
        for (let z = e0; z <= rl; z++) if (ok(R(z))) { lvE.push(Lv(z + L)); const d = fold(T(z + L) - R(z)); if (ok(d) && Math.abs(d) <= K.BIAS_WIN_C) dE.push(d); }
        // the longest stretch of the melody without a pause to breathe
        let run = 0, best = 0, gp = 0, st = rf;
        for (let z = rf; z <= rl; z++) { if (ok(R(z))) { if (gp >= f(K.BREATH_GAP_MS)) st = z; gp = 0; best = Math.max(best, z - st + 1); } else gp++; }
        run = best * HOP_MS / 1000;
        const cut = hl < 0 ? span * HOP_MS : (rl + L - hl) * HOP_MS;
        const fallDb = lvM.length && lvE.length ? med(lvE) - med(lvM) : NaN, fallC = dM.length >= 10 && dE.length >= 5 ? med(dE) - med(dM) : NaN;
        ends.push({ line: s.n, cutMs: Math.round(cut), fallDb: r1(fallDb), fallC: r0(fallC), runS: r1(run),
          cut: cut >= K.CUT_MS, fade: fallDb <= -K.END_FALL_DB_FLAG, sag: fallC <= -K.END_FALL_C_FLAG });
      }
    });

    // pitch bias: overall and per third of his range (by the pitch he sang); the note histogram (for the range)
    for (const [x, y, d] of pairsAll) {
      const m = Math.round(midiOf(T(y))), h = hist[m] || (hist[m] = [0, 0, 0, 0]); // [frames, in tune, frames within BIAS_WIN_C, sum of their deviation]
      h[0]++; if (Math.abs(d) <= K.IN_TUNE_C) h[1]++; if (Math.abs(d) <= K.BIAS_WIN_C) { h[2]++; h[3] += d; }
    }
    for (const k of Object.keys(hist)) hist[k][3] = Math.round(hist[k][3]);
    // entries: his voiced-run start near each melody entry -> timing; the first 300 ms vs the target -> scoop / clean
    const ent = [], B = inp.base || null, tb = B && Number.isFinite(B.timing) ? Math.round(B.timing) : 0;
    for (const o of onsets) {
      let best = null;
      for (let d = -f(K.ONSET_MATCH_MS); d <= f(K.ONSET_MATCH_MS); d++) {
        const u = o.x + d; if (!ok(T(u)) || ok(T(u - 1))) continue;
        if (best == null || Math.abs(d) < Math.abs(best)) best = d;
      }
      if (best == null) continue;
      // vs the melody's own entry contour (its frame k after its entry): a scoop the original singer does is the song's,
      // not his; where the melody has no confident frame, its note target
      const u = o.x + best, e = (k) => { const rv = R(o.x + k); return fold(T(u + k) - (ok(rv) ? rv : o.target)); };
      let depth = 0; for (let k = 0; k < f(K.SCOOP_LOOK_MS); k++) { const v = e(k); if (ok(v)) depth = Math.max(depth, -v); }
      let reach = -1; for (let k = 0; k < f(K.SCOOP_WIN_MS); k++) { const v = e(k); if (ok(v) && Math.abs(v) <= K.SCOOP_REACH_C) { reach = k * HOP_MS; break; } }
      const onBeat = beats.some((b) => Math.abs(b * 1000 - o.x * HOP_MS) <= K.BEAT_NEAR_MS);
      ent.push({ line: o.line, off: best * HOP_MS - tb, depth: Math.round(depth), reach, onBeat,
        scoop: depth >= K.SCOOP_C && reach >= K.SCOOP_MS, clean: reach >= 0 && reach <= K.CLEAN_ENTRY_MS });
    }
    // the song's melody (whole song, original key) in the octave he sings it: for a key suggestion
    lines.forEach((s) => { const e = ent.filter((q) => q.line === s.n); if (s.rec && e.length) s.tim = Math.round(mean(e.map((q) => q.off))); });
    const octs = pairsAll.map(([x, y]) => Math.round((T(y) - R(x)) / 1200)), oct = octs.length ? Math.round(med(octs)) : 0;
    const mel = {}, tr = meta.transpose || 0;
    for (let x = 0; x < ref.cents.length; x++) { const v = R(x); if (!ok(v)) continue; const m = Math.round(midiOf(v - 100 * tr + 1200 * oct)); mel[m] = (mel[m] || 0) + 1; }

    const res = { v: VOICE_V, takeId: meta.takeId || null, songId: meta.songId || null, created: meta.created || null, at: Date.now(),
      src: meta.src || 'a', mode: meta.mode || null, transpose: tr,
      // entry timing is trusted when the take's latency was measured and the song did not come out of the speaker
      timingTrust: meta.mode !== 'speaker' && meta.latSource !== 'estimate', nudgeMs: inp.nudgeMs || 0, latSource: meta.latSource || null,
      takeSec: r1(tn / 100), voicedSec: r1(framesV / 100), oct,
      lines: lines.map((s) => (s.rec ? s : { n: s.n, t0: s.t0, t1: s.t1, rec: false })),
      base: B, hist, mel, held: held.map((h) => ({ line: h.line, jit: r1(h.jit), refJit: r1(h.refJit), drop: r0(h.drop) })), ent, ends, ms: 0 };
    res.m = measures(res);
    res.ms = Date.now() - t0;
    return res;
  }

  // ---- measures from one or many takes (the same code: a single take is a list of one)
  function measures(a) { // a: one analysis, or the merged { hist, held, ent, ends, lines?, takes }
    const H = a.hist, notes = Object.keys(H).map(Number).sort((x, y) => x - y);
    let n = 0, nIn = 0, nB = 0, sB = 0; for (const k of notes) { n += H[k][0]; nIn += H[k][1]; nB += H[k][2]; sB += H[k][3]; }
    // his range (by the frames he sang), 5th–95th percentile, split in thirds
    const pct = (p) => { let c = 0; const goal = p * n; for (const k of notes) { c += H[k][0]; if (c >= goal) return k; } return notes[notes.length - 1]; };
    const lo = pct(0.05), hi = pct(0.95), w = (hi - lo + 1) / 3, third = (k) => (k < lo ? 0 : k > hi ? 2 : Math.min(2, Math.floor((k - lo) / w)));
    const reg = [0, 1, 2].map((i) => {
      let rn = 0, rs = 0, rf = 0, a = Infinity, b = -Infinity;
      for (const k of notes) if (third(k) === i) { rn += H[k][2]; rs += H[k][3]; rf += H[k][0]; if (k >= lo && k <= hi) { a = Math.min(a, k); b = Math.max(b, k); } }
      return { from: Number.isFinite(a) ? a : null, to: Number.isFinite(b) ? b : null, n: rn, frames: rf, bias: rn ? r1(rs / rn) : null };
    });
    // comfortable range: notes sung >= RANGE_MIN_FRAMES with >= RANGE_IN_TUNE in tune
    const comf = notes.filter((k) => H[k][0] >= K.RANGE_MIN_FRAMES && H[k][1] / H[k][0] >= K.RANGE_IN_TUNE);
    const hd = (a.held || []).filter((h) => h.jit != null), dr = (a.held || []).filter((h) => h.drop != null);
    const en = (a.ent || []), sc = en.filter((e) => e.reach !== undefined), ET = a.entT || en, offs = ET.map((e) => e.off), bt = ET.filter((e) => e.onBeat).map((e) => e.off);
    const eds = (a.ends || []);
    const lsc = (a.lines || []).filter((s) => s.rec);
    return {
      frames: n, pIn: n ? Math.round(100 * nIn / n) : null, bias: nB ? r1(sB / nB) : null, biasN: nB, reg,
      range: comf.length ? { lo: comf[0], hi: comf[comf.length - 1], n: comf.length } : null, sungLo: lo, sungHi: hi,
      jitter: { n: hd.length, mean: r1(mean(hd.map((h) => h.jit))), ref: r1(mean(hd.map((h) => h.refJit))), drop: r1(mean(dr.map((h) => h.drop))), dropN: dr.length },
      scoop: { n: sc.length, rate: sc.length ? r1(100 * sc.filter((e) => e.scoop).length / sc.length) : null, clean: sc.length ? r1(100 * sc.filter((e) => e.clean).length / sc.length) : null,
        depth: r0(mean(sc.filter((e) => e.scoop).map((e) => e.depth))), reach: r0(mean(sc.filter((e) => e.scoop).map((e) => e.reach))) },
      timing: { n: offs.length, mean: r0(mean(offs)), med: r0(med(offs)), sd: r0(sd(offs)), late: offs.length ? r0(100 * offs.filter((x) => x > 0).length / offs.length) : null,
        early: offs.length ? r0(100 * offs.filter((x) => x < 0).length / offs.length) : null, beatN: bt.length, beatMean: r0(mean(bt)) },
      ends: { n: eds.length, cutRate: eds.length ? r0(100 * eds.filter((e) => e.cut).length / eds.length) : null, fadeRate: eds.length ? r0(100 * eds.filter((e) => e.fade).length / eds.length) : null,
        sagRate: eds.length ? r0(100 * eds.filter((e) => e.sag).length / eds.length) : null, fallDb: r1(med(eds.map((e) => e.fallDb).filter((x) => x != null))),
        fallC: r0(med(eds.map((e) => e.fallC).filter((x) => x != null))),
        breath: eds.filter((e) => (e.cut || e.fade) && e.runS >= K.BREATH_RUN_S).map((e) => e.line), long: eds.filter((e) => e.runS >= K.LONG_RUN_S).map((e) => e.line) },
      base: a.base || null, timingTrust: a.timingTrust !== false,
      lines: { n: lsc.length, sung: lsc.filter((s) => s.col !== 'grey').length, green: lsc.filter((s) => s.col === 'green').length, yellow: lsc.filter((s) => s.col === 'yellow').length, red: lsc.filter((s) => s.col === 'red').length, grey: lsc.filter((s) => s.col === 'grey').length },
    };
  }

  // ---- many takes (all songs): sum the histograms, pool the events; per-take series for the progress charts
  function aggregate(list) {
    const ok = list.filter((a) => a && a.v === VOICE_V && a.m);
    const hist = {}, held = [], ent = [], ends = [];
    for (const a of ok) {
      for (const [k, h] of Object.entries(a.hist || {})) { const g = hist[k] || (hist[k] = [0, 0, 0, 0]); for (let i = 0; i < 4; i++) g[i] += h[i]; }
      held.push(...(a.held || [])); ent.push(...(a.ent || [])); ends.push(...(a.ends || []));
    }
    // entry TIMING: from the takes whose timing can be trusted (headphones, measured latency); none such: all, flagged unsure
    const trusted = ok.filter((a) => a.timingTrust !== false), entT = [];
    (trusted.length ? trusted : ok).forEach((a) => entT.push(...(a.ent || [])));
    // the original singers' rates, pooled with the same weights as his (entries / line endings per take)
    const pool = (key, w) => { let n = 0, s = 0; for (const a of ok) { const b = a.base, k = w(a); if (b && b[key] != null && k) { n += k; s += b[key] * k; } } return n ? Math.round(s / n) : null; };
    const base = { src: 'pooled', scoop: pool('scoop', (a) => (a.ent || []).length), cut: pool('cut', (a) => (a.ends || []).length), fade: pool('fade', (a) => (a.ends || []).length), sag: pool('sag', (a) => (a.ends || []).length) };
    const merged = { hist, held, ent, entT, ends, base };
    const m = measures(merged);
    m.timingTrust = trusted.length > 0; m.timingTakes = (trusted.length ? trusted : ok).length;
    m.takes = ok.length; m.songs = [...new Set(ok.map((a) => a.songId))].length; m.voicedSec = r1(ok.reduce((p, a) => p + (a.voicedSec || 0), 0));
    m.lines = { n: 0 }; // lines belong to a song's take, not to the pool
    const series = ok.slice().sort((p, q) => (p.created || 0) - (q.created || 0)).map((a) => ({ takeId: a.takeId, songId: a.songId, created: a.created,
      pIn: a.m.pIn, bias: a.m.bias, jitter: a.m.jitter.mean, scoop: a.m.scoop.rate, timing: a.m.timing.mean, cut: a.m.ends.cutRate, voicedSec: a.voicedSec }));
    // a key per song: the shift (−6..+6) that puts most of the song's melody in his comfortable range
    const keys = [];
    const bySong = new Map(); for (const a of ok) { const p = bySong.get(a.songId); if (!p || (a.created || 0) > (p.created || 0)) bySong.set(a.songId, a); }
    if (m.range) bySong.forEach((a, sid) => { const k = keyFor(a.mel, m.range); if (k) keys.push({ songId: sid, ...k }); });
    m.keys = keys;
    return { m, series, takes: ok.length };
  }
  function keyFor(mel, range) {
    const ks = Object.keys(mel || {}).map(Number), tot = ks.reduce((p, k) => p + mel[k], 0); if (!tot || !range) return null;
    const fit = (s) => ks.reduce((p, k) => p + (k + s >= range.lo && k + s <= range.hi ? mel[k] : 0), 0) / tot;
    let best = 0, bf = fit(0);
    for (let s = -6; s <= 6; s++) { const v = fit(s); if (v > bf + 1e-9 || (Math.abs(v - bf) < 1e-9 && Math.abs(s) < Math.abs(best))) { best = s; bf = v; } }
    const fits = []; for (let s = -6; s <= 6; s++) fits.push(Math.round(100 * fit(s)));
    return { best, fitBest: Math.round(100 * bf), fits }; // fits[s + 6] = % of the melody in range at shift s
  }
  const fitAt = (k, s) => k.fits[Math.max(-6, Math.min(6, s)) + 6];
  // how much singing stands behind a report: 0 thin .. 2 solid (a single take: by its voiced seconds; many: also by takes)
  function capFor(voicedSec, takes) {
    const v = voicedSec >= 90 ? 2 : voicedSec >= 30 ? 1 : 0;
    return takes == null ? Math.min(v, 1) : Math.min(v, conf(takes, K.CONF_N.takes)); // one take alone is never "high"
  }

  // the song's original singer through analyse() (his own vocal stem as the "take", no base) -> the base for his takes
  function baseline(res) {
    const m = res.m;
    return { v: VOICE_V, src: 'orig', at: Date.now(), timing: m.timing.n ? m.timing.mean : K.BASE_DEFAULT.timing, nEnt: m.timing.n, scoop: m.scoop.rate, cut: m.ends.cutRate, fade: m.ends.fadeRate, sag: m.ends.sagRate,
      nEnds: m.ends.n, jitter: m.jitter.mean, pIn: m.pIn, bias: m.bias, ms: res.ms };
  }

  // ---- findings: measures -> ranked findings (each with its exercises); conservative, with a confidence level
  const CONF_HE = ['ביטחון נמוך: מעט נתונים', 'ביטחון בינוני', 'ביטחון גבוה'];
  const LR = (s) => '⁦' + s + '⁩'; // LTR isolate for numbers with signs inside Hebrew text
  const sgn = (x) => (x > 0 ? '+' : x < 0 ? '−' : '') + Math.abs(x);
  const NOTE = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B'];
  const noteName = (m) => NOTE[((Math.round(m) % 12) + 12) % 12] + (Math.floor(Math.round(m) / 12) - 1);
  function findings(m, scope) { // scope: { takes, curKey?, songId?, keyHere? } -> [{ id, sev, conf, title, text, ex: [ids] }]
    // confidence: the measure's own amount of data, capped by the amount of singing behind it (scope.cap: 0..2)
    const out = [], cap = scope && scope.cap != null ? scope.cap : 2;
    const fc = (n, which) => Math.min(conf(n, K.CONF_N[which]), cap);
    // pitch tendency: when the registers differ (spread >= REG_SPREAD_C) the registers speak (neighbours with the same
    // direction as one finding), otherwise the overall bias does — never both
    const names = ['הנמוכים', 'האמצעיים', 'הגבוהים'], RG = m.reg.map((g, i) => ({ ...g, i })).filter((g) => g.bias != null && g.from != null && g.n >= K.REG_MIN_FRAMES);
    const spread = RG.length >= 2 ? Math.max(...RG.map((g) => g.bias)) - Math.min(...RG.map((g) => g.bias)) : 0;
    if (spread >= K.REG_SPREAD_C) {
      const flag = RG.filter((g) => Math.abs(g.bias) >= K.REG_BIAS_FLAG_C), groups = [];
      flag.forEach((g) => { const last = groups[groups.length - 1]; if (last && last[last.length - 1].i === g.i - 1 && Math.sign(last[0].bias) === Math.sign(g.bias)) last.push(g); else groups.push([g]); });
      groups.forEach((gs) => {
        const flat = gs[0].bias < 0, n = gs.reduce((p, g) => p + g.n, 0), b = gs.reduce((p, g) => p + g.bias * g.n, 0) / n, top = gs[gs.length - 1].i;
        out.push({ id: (flat ? 'flat' : 'sharp') + ['Low', 'Mid', 'High'][top], sev: Math.min(1, Math.abs(b) / 60) + (top === 2 ? 0.1 : 0), conf: fc(n, 'regFrames'),
          title: 'בצלילים ' + gs.map((g) => names[g.i]).join(' ו') + ' שלך: ' + (flat ? 'נמוך מהטון' : 'גבוה מהטון'),
          text: 'בטווח ' + LR(noteName(gs[0].from) + '–' + noteName(gs[gs.length - 1].to)) + ' בממוצע ' + LR(sgn(Math.round(b))) + ' סנט' + ' מהמנגינה (100 סנט = חצי טון)' + (RG.some((g) => Math.abs(g.bias) < K.REG_BIAS_FLAG_C / 2) ? '; בשאר הטווח מדויק.' : '.'),
          ex: flat ? (top === 2 ? ['sirens', 'lipTrills'] : ['support', 'longTones']) : (top === 2 ? ['lipTrills', 'listenFirst'] : ['listenFirst', 'longTones']) });
      });
    } else if (m.bias != null && Math.abs(m.bias) >= K.BIAS_FLAG_C) {
      const sharp = m.bias > 0;
      out.push({ id: sharp ? 'sharp' : 'flat', sev: Math.min(1, Math.abs(m.bias) / 50), conf: fc(m.biasN, 'frames'),
        title: sharp ? 'נוטה לשיר מעט גבוה מהטון' : 'נוטה לשיר מעט נמוך מהטון',
        text: 'בממוצע ' + LR(sgn(Math.round(m.bias))) + ' סנט' + ' מהמנגינה (100 סנט = חצי טון), בכל הטווח.', ex: sharp ? ['listenFirst', 'longTones'] : ['support', 'longTones'] });
    }
    const j = m.jitter;
    if (j.n && j.mean >= K.JITTER_FLAG_C && j.mean >= (j.ref || 0) + K.JITTER_OVER_REF_C) {
      out.push({ id: 'unsteady', sev: Math.min(1, (j.mean - (j.ref || 0)) / 30), conf: fc(j.n, 'held'), title: 'צלילים ארוכים לא יציבים',
        text: 'בצלילים ארוכים הגובה נע בממוצע ' + LR('±' + Math.round(j.mean)) + ' סנט' + ' (בשירה המקורית ' + LR('±' + Math.round(j.ref || 0)) + '), ב-' + j.n + ' צלילים.', ex: ['longTones', 'support'] });
    }
    if (j.dropN && j.drop <= -K.END_DROP_FLAG_C) {
      out.push({ id: 'noteSag', sev: Math.min(1, -j.drop / 60), conf: fc(j.dropN, 'held'), title: 'סוף הצליל הארוך יורד',
        text: 'ב-150 ms האחרונים של צליל ארוך: בממוצע ' + LR(sgn(Math.round(j.drop))) + ' סנט' + ' לעומת אמצע הצליל.', ex: ['support', 'longTones'] });
    }
    const s = m.scoop, B = m.base || {}, over = (rate, b) => rate >= Math.max(100 * K.SCOOP_RATE_FLAG, (b || 0) + K.OVER_BASE_PCT);
    if (s.n && over(s.rate, B.scoop)) {
      out.push({ id: 'scoop', sev: Math.min(1, (s.rate - (B.scoop || 0)) / 50), conf: fc(s.n, 'onsets'), title: 'כניסות "מלמטה" (גלישה אל הצליל)',
        text: Math.round(s.rate) + '% מהכניסות מתחילות כ-' + LR(s.depth) + ' סנט' + ' מתחת לצליל ומגיעות אליו אחרי כ-' + LR(s.reach + ' ms') + ' (' + s.n + ' כניסות' + (B.scoop != null ? '; בשירה המקורית ' + Math.round(B.scoop) + '%' : '') + ').', ex: ['humAttack', 'targetStart'] });
    }
    const t = m.timing, latUnsure = scope && scope.latUnsure != null ? scope.latUnsure : m.timingTrust === false;
    if (t.n && Math.abs(t.mean) >= K.TIMING_FLAG_MS && (t.mean > 0 ? t.late : t.early) >= 100 * K.TIMING_CONSIST) {
      const late = t.mean > 0;
      out.push({ id: late ? 'late' : 'early', sev: Math.min(1, Math.abs(t.mean) / 80), conf: Math.min(fc(t.n, 'onsets'), latUnsure ? 0 : 2),
        title: late ? 'נכנס מעט אחרי הקצב' : 'נכנס מעט לפני הקצב',
        text: 'בממוצע ' + LR(Math.abs(t.mean) + ' ms') + (late ? ' אחרי' : ' לפני') + ' הזמר המקורי (' + (late ? t.late : t.early) + '% מ-' + t.n + ' כניסות).' + (latUnsure ? ' (הוקלט ברמקול או בלי כיול: ייתכן שזו השהיית המכשיר ולא השירה — כדאי לבדוק באוזניות אחרי כיול)' : ''), ex: ['clapCount', 'loopLine'] });
    }
    const e = m.ends;
    const eo = (rate, b) => rate >= Math.max(100 * K.CUT_RATE_FLAG, (b || 0) + K.OVER_BASE_PCT), oC = e.n && eo(e.cutRate, B.cut), oF = e.n && eo(e.fadeRate, B.fade), oS = e.n && eo(e.sagRate, B.sag);
    if (oC || oF || oS) {
      const orig = (b) => (b != null ? ' (במקור ' + Math.round(b) + '%)' : '');
      const what = [oC ? e.cutRate + '% מהשורות נגמרות מוקדם' + orig(B.cut) : '', oF ? e.fadeRate + '% דועכות בסוף' + orig(B.fade) : '', oS ? e.sagRate + '% יורדות בגובה בסוף' + orig(B.sag) : ''].filter(Boolean).join(', ');
      out.push({ id: 'phraseEnd', sev: Math.min(1, Math.max(oC ? e.cutRate - (B.cut || 0) : 0, oF ? e.fadeRate - (B.fade || 0) : 0, oS ? e.sagRate - (B.sag || 0) : 0) / 50), conf: fc(e.n, 'lines'), title: 'סופי שורות: נגמר האוויר?',
        text: what + '.' + (e.breath.length ? ' שורות שאולי ארוכות לנשימה אחת: ' + LR(e.breath.slice(0, 6).join(', ')) + '.' : ''), ex: ['breath48', 'phraseMark'] });
    } else if (e.long && e.long.length) {
      out.push({ id: 'longLines', tip: true, sev: 0.15, conf: 1, title: 'שורות ארוכות בלי מקום לנשום', text: 'שורות ' + LR(e.long.slice(0, 6).join(', ')) + ': כדאי לתכנן מראש איפה נושמים.', ex: ['phraseMark'] });
    }
    const kh = scope && scope.keyHere, cur = (scope && scope.curKey) || 0;
    if (kh && kh.best !== cur && kh.fitBest - fitAt(kh, cur) >= 100 * K.RANGE_FIT_GAIN) {
      out.push({ id: 'key', sev: Math.min(1, (kh.fitBest - fitAt(kh, cur)) / 30), conf: Math.min(m.range && m.range.n >= 6 ? 1 : 0, cap), title: 'סולם נוח יותר לשיר הזה',
        text: 'בסולם ' + LR(sgn(kh.best)) + ' ' + kh.fitBest + '% מהמנגינה בטווח הנוח שלך (בסולם ' + LR(sgn(cur) || '0') + ': ' + fitAt(kh, cur) + '%).', ex: ['transpose'], key: kh.best });
    }
    if (m.pIn != null && m.pIn < 55 && !out.some((x) => /sharp|flat/.test(x.id))) {
      out.push({ id: 'accuracy', sev: Math.min(1, (60 - m.pIn) / 40), conf: fc(m.frames, 'frames'), title: 'דיוק כללי בגובה', text: m.pIn + '% מהשירה בטון (±50 סנט).', ex: ['targetStart', 'loopLine'] });
    }
    // rank: severity, weighted by confidence (thin data never tops solid data)
    out.forEach((x) => { x.rank = x.sev * [0.5, 0.8, 1][x.conf]; x.confText = CONF_HE[x.conf]; });
    out.sort((a, b) => b.rank - a.rank);
    return out;
  }

  // ---- the exercise library (Hebrew; plain wording, no medical claims). tool: what the app can do for it right away
  const EX = {
    sirens: { name: 'סירנות', how: 'על "ווו" או "נג", גלישה רכה מהצליל הנמוך שלך לגבוה וחזרה, 5–6 פעמים, בלי לדחוף.', why: 'מחברת את האזורים של הקול, כך שהצלילים הגבוהים מגיעים בלי מאמץ ובלי ליפול מתחת לטון.' },
    lipTrills: { name: 'טרילים בשפתיים', how: 'שפתיים רפויות ו"ברררר" על המנגינה של השורה (או גלישה למעלה ולמטה), 1–2 דקות.', why: 'שומר על זרימת אוויר אחידה ועל גרון רפוי — עוזר לצלילים גבוהים להיות מדויקים.' },
    support: { name: 'תמיכה נשימתית', how: 'שאיפה לבטן ולצלעות (לא לכתפיים), ואז "ססס" ארוך ואחיד; אחר כך אותה תחושה בזמן שירת השורה.', why: 'אוויר יציב = גובה יציב. צלילים שיורדים מהטון הם לעיתים קרובות סימן שהאוויר נחלש.' },
    longTones: { name: 'צלילים ארוכים מול צליל קבוע', how: 'מנגנים צליל (🎵 צליל מטרה) ושרים איתו 6–8 שניות על "אָה", מנסים שהקול לא ינוע. 5 צלילים שונים.', why: 'מאמן את האוזן ואת השליטה להחזיק גובה אחד בלי לרעוד או לרדת.', tool: 'tone' },
    listenFirst: { name: 'קודם לשמוע, אחר כך לשיר', how: 'לשמוע את צליל הפתיחה (🎵), לשיר אותו בשקט בראש, ורק אז בקול — רך, בלי לדחוף.', why: 'שירה גבוהה מהטון באה הרבה פעמים מלחץ או מעוצמה; כניסה רכה מכוונת טוב יותר.', tool: 'tone' },
    humAttack: { name: 'זמזום ואז כניסה', how: 'לזמזם (פה סגור) את הצליל של תחילת השורה, ואז לפתוח ל"אָה" באותו גובה בדיוק. כשזה יציב — עם המילים.', why: 'הזמזום "ממקם" את הצליל לפני שהקול נכנס, כך שאין צורך לגלוש אליו מלמטה.', tool: 'tone' },
    targetStart: { name: 'להתחיל ישר בגובה', how: 'עם תצוגת 🎯 פועלת: לשיר רק את המילה הראשונה של השורה, שוב ושוב, עד שהנקודות ירוקות מההתחלה.', why: 'רואים מיד אם הכניסה מדויקת — וכך לומדים לפגוע בצליל בלי לחפש אותו.', tool: 'loop' },
    breath48: { name: 'שאיפה 4, נשיפה 8', how: 'שאיפה בספירה של 4, נשיפה איטית על "ססס" בספירה של 8. 5 פעמים, ואז להאריך ל-10 ול-12.', why: 'מלמד לחלק את האוויר לאורך כל השורה, כך שהסוף לא נחלש.' },
    phraseMark: { name: 'לסמן נשימות', how: 'להחליט מראש איפה נושמים בשורה (בהפסקה קטנה במנגינה), לסמן לעצמך ולתרגל עם 🔁 על השורה.', why: 'נשימה מתוכננת לא "נגנבת" מסוף המשפט — הסוף נשאר מלא ובגובה.', tool: 'loop' },
    clapCount: { name: 'מחיאות עם הביט', how: 'לנגן את השורה, למחוא כפיים על כל פעמה ולספור בקול; אחר כך לשיר ולשים לב שהכניסה נופלת על הפעמה. אפשר להפעיל "ספירה לפני כל חזרה".', why: 'מחבר את הכניסות לקצב של השיר במקום להגיב אליו באיחור.', tool: 'loop' },
    loopLine: { name: 'חזרה על שורה', how: 'לבחור שורה מהרשימה (🔁) ולשיר אותה 5 פעמים ברצף; אפשר גם בקצב איטי יותר בהשמעה.', why: 'חזרה קצרה וממוקדת מתקנת יותר מעוד הקלטה של כל השיר.', tool: 'loop' },
    transpose: { name: 'לנסות סולם אחר', how: 'להחיל את הסולם המוצע בלחיצה ולשיר את השיר שוב; להשוות את הדוח.', why: 'כשרוב המנגינה יושבת בטווח הנוח, הקול פנוי לדיוק ולהבעה במקום להיאבק בקצוות.', tool: 'transpose' },
  };

  const API = { VOICE_V, K, analyse, measures, aggregate, findings, baseline, keyFor, fitAt, capFor, lineColour, combine, EX, noteName, CONF_HE };
  if (typeof module !== 'undefined' && module.exports) module.exports = API;
  else root.HarmonyVoice = API;
})(typeof self !== 'undefined' ? self : this);
