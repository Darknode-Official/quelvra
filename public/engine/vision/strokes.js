// Quelvra vision: online handwriting recognition for canvas strokes.
//
//   recognizeStrokes(strokes, opts) -> { text, symbols, lowConfidence, layout, em }
//   addTemplate(char, strokes), exportUserTemplates(), importUserTemplates(json)
//
// strokes: [[{x, y, t?}, ...], ...] in canvas pixels (y down), in writing order.
// Pipeline:
//   1. clean the strokes and guess the writing size (em);
//   2. segment consecutive strokes into symbols with dynamic programming: every run of 1..4
//      consecutive, spatially overlapping strokes is a candidate symbol whose cost is its best
//      $P point-cloud match (Vatavu, Anthony, Wobbrock 2012) against templates with the SAME
//      stroke count, plus a size-plausibility penalty and a per-symbol penalty, so "=" beats
//      two "-" and "i" beats "1" + ".";
//   3. re-run with the text size estimated from the first pass (size cues separate "." from "o",
//      "," from ")", "c" from "(");
//   4. hand the symbols to layout.js for superscripts, subscripts, fractions and radicals.
// Every symbol reports a confidence and its top alternatives; symbols below the threshold are
// listed in lowConfidence. Nothing is solved here.

import { VARIANTS, METRICS, typeset } from "./glyphs.js";
import { analyzeLayout, estimateEm, contextRerank } from "./layout.js";

const NP = 32;       // points per cloud (fine pass)
const NC = 16;       // points per cloud (coarse pass)
const SHORTLIST = 28;
const SYMBOL_PENALTY = 0.05;
const POWER = 6;      // sharpness of the distance-ratio probabilities
const DIST_FLOOR = 0.02;
const PRIORS = { l: 0.002, "|": 0.002, "^": 0.01, ",": 0.005 }; // small biases toward the commoner reading
export const LOW_CONFIDENCE = 0.7;

// ---------------------------------------------------------------------------------------------
// $P point clouds
function flatten(strokes) {
  const pts = [];
  strokes.forEach((s, id) => { for (const p of s) pts.push({ x: p.x, y: p.y, id }); });
  return pts;
}
function pathLength(pts) {
  let d = 0;
  for (let i = 1; i < pts.length; i++) if (pts[i].id === pts[i - 1].id) d += Math.hypot(pts[i].x - pts[i - 1].x, pts[i].y - pts[i - 1].y);
  return d;
}
function resample(pts, n) {
  const I = pathLength(pts) / (n - 1);
  if (!(I > 1e-9)) {
    const c = centroid(pts);
    return Array.from({ length: n }, () => ({ x: c.x, y: c.y, id: 0 }));
  }
  const src = pts.map((p) => ({ ...p }));
  const out = [{ ...src[0] }];
  let D = 0;
  for (let i = 1; i < src.length; i++) {
    if (src[i].id !== src[i - 1].id) continue;
    const d = Math.hypot(src[i].x - src[i - 1].x, src[i].y - src[i - 1].y);
    if (D + d >= I && d > 0) {
      const t = (I - D) / d;
      const q = { x: src[i - 1].x + t * (src[i].x - src[i - 1].x), y: src[i - 1].y + t * (src[i].y - src[i - 1].y), id: src[i].id };
      out.push(q);
      src.splice(i, 0, q);
      D = 0;
    } else D += d;
  }
  while (out.length < n) out.push({ ...src[src.length - 1] });
  return out.slice(0, n);
}
function centroid(pts) {
  let x = 0, y = 0;
  for (const p of pts) { x += p.x; y += p.y; }
  return { x: x / pts.length, y: y / pts.length };
}
function normalize(pts) {
  let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
  for (const p of pts) { if (p.x < x0) x0 = p.x; if (p.y < y0) y0 = p.y; if (p.x > x1) x1 = p.x; if (p.y > y1) y1 = p.y; }
  const s = Math.max(x1 - x0, y1 - y0) || 1;
  const c = centroid(pts);
  return pts.map((p) => ({ x: (p.x - c.x) / s, y: (p.y - c.y) / s, id: p.id }));
}
function cloud(strokes, n) { return normalize(resample(flatten(strokes), n)); }

// Two global shape features that $P (uniform scaling, point-set matching) is weak at: thin
// symbols ("1", "|", "/", "(", "∫", "l") differ in aspect ratio and straightness
// (chord length / path length), which are cheap and stable under jitter. Turning angle and
// principal-axis orientation were tried and hurt accuracy (too noise-sensitive).
function features(strokes) {
  const pts = resample(flatten(strokes), 20);
  let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
  for (const p of pts) { if (p.x < x0) x0 = p.x; if (p.y < y0) y0 = p.y; if (p.x > x1) x1 = p.x; if (p.y > y1) y1 = p.y; }
  const S = Math.max(x1 - x0, y1 - y0) || 1, eps = 0.06 * S;
  const aspect = Math.log((x1 - x0 + eps) / (y1 - y0 + eps));
  let chord = 0, path = 0;
  for (let i = 1; i < pts.length; i++) if (pts[i].id === pts[i - 1].id) path += Math.hypot(pts[i].x - pts[i - 1].x, pts[i].y - pts[i - 1].y);
  for (const id of new Set(pts.map((p) => p.id))) {
    const q = pts.filter((p) => p.id === id);
    chord += Math.hypot(q[q.length - 1].x - q[0].x, q[q.length - 1].y - q[0].y);
  }
  return [aspect, path > 0 ? chord / path : 1];
}
const FW = [0.01, 0.03];
function featureDistance(a, b) {
  let d = 0;
  for (let i = 0; i < FW.length; i++) d += FW[i] * Math.abs(a[i] - b[i]);
  return d;
}

function cloudDistance(a, b, start, bound) {
  const n = a.length;
  const matched = new Uint8Array(n);
  let sum = 0, i = start;
  do {
    let min = Infinity, idx = -1;
    const ax = a[i].x, ay = a[i].y;
    for (let j = 0; j < n; j++) {
      if (matched[j]) continue;
      const dx = ax - b[j].x, dy = ay - b[j].y, d = dx * dx + dy * dy;
      if (d < min) { min = d; idx = j; }
    }
    matched[idx] = 1;
    const w = 1 - ((i - start + n) % n) / n;
    sum += w * Math.sqrt(min);
    if (sum >= bound) return sum;
    i = (i + 1) % n;
  } while (i !== start);
  return sum;
}
function greedyMatch(a, b, bound = Infinity) {
  const n = a.length;
  const step = Math.max(1, Math.floor(Math.sqrt(n)));
  let min = bound;
  for (let i = 0; i < n; i += step) {
    const d1 = cloudDistance(a, b, i, min);
    if (d1 < min) min = d1;
    const d2 = cloudDistance(b, a, i, min);
    if (d2 < min) min = d2;
  }
  return min / n; // mean weighted distance in units of the symbol size
}

// ---------------------------------------------------------------------------------------------
// Templates
function mulberry(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

// Random writer's distortion of em-unit strokes -> pixel strokes (y down).
// Exported so tests (and a future "practice" UI) synthesize handwriting the same way.
export function distortStrokes(emStrokes, rand, { em = 40, rot = 6, shear = 0.12, aniso = 0.1, jitter = 0.012, wobble = 0.02, x = 0, y = 0 } = {}) {
  const g = () => { let s = 0; for (let k = 0; k < 4; k++) s += rand(); return (s - 2) * 1.7; };
  const a = (g() * rot * Math.PI) / 180, sh = g() * shear;
  const sx = em * (1 + g() * aniso), sy = em * (1 + g() * aniso);
  const c = Math.cos(a), s = Math.sin(a);
  const ph1 = rand() * 6.28, ph2 = rand() * 6.28, f = 3 + rand() * 4;
  return emStrokes.map((st) => {
    const off = [g() * jitter * 2, g() * jitter * 2];
    let pts = st.map(([px, py], k) => {
      const u = k / Math.max(1, st.length - 1);
      const wx = px + off[0] + wobble * Math.sin(f * u * 6.28 + ph1) + g() * jitter;
      const wy = py + off[1] + wobble * Math.sin(f * u * 6.28 + ph2) + g() * jitter;
      const qx = wx + sh * wy, qy = wy;
      const rx = c * qx - s * qy, ry = s * qx + c * qy;
      return { x: x + rx * sx, y: y - ry * sy };
    });
    if (rand() < 0.3) pts = pts.reverse();
    return pts;
  });
}

// Synthesize handwriting for a typeset spec (see glyphs.typeset): every glyph gets its own
// random distortion about its own centre, plus a small random displacement. Returns strokes in
// writing order (pixels, y down) and the ground-truth glyph list.
export function synthesizeStrokes(spec, rand, { em = 40, x = 30, y = null, drift = 0.04, ...distort } = {}) {
  const t = typeset(spec, { em: 1, x: 0, y: 0, rng: rand });
  const baseY = y == null ? 30 + em * 1.6 : y;
  const strokes = [], truth = [];
  for (const g of t.glyphs) {
    const pts = g.strokes.map((st) => st.map((p) => [p.x, -p.y]));
    let gx0 = Infinity, gy0 = Infinity, gx1 = -Infinity, gy1 = -Infinity;
    for (const st of pts) for (const [a, b] of st) { gx0 = Math.min(gx0, a); gy0 = Math.min(gy0, b); gx1 = Math.max(gx1, a); gy1 = Math.max(gy1, b); }
    const cxm = (gx0 + gx1) / 2, cym = (gy0 + gy1) / 2;
    const local = pts.map((st) => st.map(([a, b]) => [a - cxm, b - cym]));
    const dx = (rand() - 0.5) * 2 * drift, dy = (rand() - 0.5) * 2 * drift;
    const out = distortStrokes(local, rand, { em, x: x + (cxm + dx) * em, y: baseY - (cym + dy) * em, ...distort });
    truth.push({ char: g.char, strokeIds: out.map((_, k) => strokes.length + k) });
    strokes.push(...out);
  }
  return { strokes, truth };
}

function emToPixels(strokes) { return strokes.map((s) => s.map(([x, y]) => ({ x: x * 100, y: -y * 100 }))); }
function naturalSize(strokes) {
  let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
  for (const s of strokes) for (const [x, y] of s) { if (x < x0) x0 = x; if (y < y0) y0 = y; if (x > x1) x1 = x; if (y > y1) y1 = y; }
  return Math.max(x1 - x0, y1 - y0);
}

// Stroke structure: each stroke's bounding box relative to the whole symbol (centre-origin,
// scaled by the symbol's larger side). Compared under the best stroke assignment, it tells a
// real "=" or "≥" apart from unrelated neighbouring strokes that happen to form a similar cloud.
function strokeBoxes(strokes) {
  const all = bboxOf(strokes);
  const S = Math.max(all.x1 - all.x0, all.y1 - all.y0) || 1;
  const cx = (all.x0 + all.x1) / 2, cy = (all.y0 + all.y1) / 2;
  return strokes.map((s) => { const b = bboxOf([s]); return [(b.x0 - cx) / S, (b.y0 - cy) / S, (b.x1 - cx) / S, (b.y1 - cy) / S]; });
}
const PERMS = { 1: [[0]], 2: [[0, 1], [1, 0]] };
function perms(n) {
  if (PERMS[n]) return PERMS[n];
  const out = [];
  const rec = (pre, rest) => { if (!rest.length) out.push(pre); rest.forEach((r, i) => rec([...pre, r], rest.filter((_, j) => j !== i))); };
  rec([], [...Array(n).keys()]);
  return (PERMS[n] = out);
}
function structureDistance(a, b) {
  if (a.length !== b.length || a.length < 2) return 0;
  let best = Infinity;
  for (const p of perms(a.length)) {
    let d = 0;
    for (let i = 0; i < a.length; i++) {
      const u = a[i], v = b[p[i]];
      d += Math.abs(u[0] - v[0]) + Math.abs(u[1] - v[1]) + Math.abs(u[2] - v[2]) + Math.abs(u[3] - v[3]);
      const su = Math.max(u[2] - u[0], u[3] - u[1], 0.03), sv = Math.max(v[2] - v[0], v[3] - v[1], 0.03);
      d += 0.4 * Math.abs(Math.log(su / sv)); // a dot is not a digit
    }
    if (d < best) best = d;
  }
  return best / (4 * a.length);
}
const STRUCT_W = 0.7;

function makeTemplate(char, pxStrokes, meta = {}) {
  return { char, n: pxStrokes.length, fine: cloud(pxStrokes, NP), coarse: cloud(pxStrokes, NC), feat: features(pxStrokes), boxes: strokeBoxes(pxStrokes), ...meta };
}

let BUILTIN = null;
const USER = []; // { char, strokes } as given by the caller (pixel coordinates)
let USER_T = [];

export function builtinTemplates({ copies = 6, seed = 7 } = {}) {
  if (BUILTIN && BUILTIN.copies === copies && BUILTIN.seed === seed) return BUILTIN.list;
  const rand = mulberry(seed);
  const list = [];
  for (const [ch, vs] of Object.entries(VARIANTS)) {
    for (const v of vs) {
      list.push(makeTemplate(ch, emToPixels(v.strokes), { variant: v.name, size: naturalSize(v.strokes) }));
      for (let k = 0; k < copies; k++) {
        const d = distortStrokes(v.strokes, rand, { em: 100, rot: 4, shear: 0.08, aniso: 0.08, jitter: 0.006, wobble: 0.012 });
        list.push(makeTemplate(ch, d, { variant: v.name + "~" + k, size: naturalSize(v.strokes) }));
      }
    }
  }
  BUILTIN = { copies, seed, list };
  return list;
}

export function addTemplate(char, strokes) {
  if (typeof char !== "string" || !char || !Array.isArray(strokes) || !strokes.length) throw new Error("addTemplate(char, strokes) needs a symbol and at least one stroke");
  const clean = cleanStrokes(strokes);
  if (!clean.length) throw new Error("addTemplate: the strokes contain no points");
  USER.push({ char, strokes: clean });
  USER_T.push(makeTemplate(char, clean, { variant: "user", user: true }));
  return USER.length;
}
export function exportUserTemplates() {
  return JSON.stringify({ format: "quelvra-stroke-templates", version: 1, templates: USER.map((u) => ({ char: u.char, strokes: u.strokes.map((s) => s.map((p) => [Math.round(p.x * 10) / 10, Math.round(p.y * 10) / 10])) })) });
}
export function importUserTemplates(json, { replace = false } = {}) {
  const o = typeof json === "string" ? JSON.parse(json) : json;
  if (!o || o.format !== "quelvra-stroke-templates" || !Array.isArray(o.templates)) throw new Error("Not a Quelvra stroke template file");
  if (replace) clearUserTemplates();
  for (const t of o.templates) addTemplate(t.char, t.strokes.map((s) => s.map(([x, y]) => ({ x, y }))));
  return USER.length;
}
export function clearUserTemplates() { USER.length = 0; USER_T = []; }
export function userTemplateCount() { return USER.length; }

// ---------------------------------------------------------------------------------------------
// Classification of one group of strokes
function bboxOf(strokes) {
  let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
  for (const s of strokes) for (const p of s) { if (p.x < x0) x0 = p.x; if (p.y < y0) y0 = p.y; if (p.x > x1) x1 = p.x; if (p.y > y1) y1 = p.y; }
  return { x0, y0, x1, y1 };
}

function sizePenalty(ch, maxDim, em) {
  if (!em) return 0;
  const m = METRICS[ch];
  if (!m) return 0;
  const s = maxDim / em;
  const lo = m.size[0] * 0.5, hi = m.size[1] * 1.35;
  let r = 0;
  if (s < lo) r = Math.log(Math.max(s, 0.01) / lo);
  else if (s > hi) r = Math.log(s / hi);
  return 0.3 * r * r + 0.12 * Math.abs(r);
}

// Returns { char, cost, ranked: [{char, dist}] } for a group of strokes, or null.
export function classifyGroup(strokes, { em = null, templates = null } = {}) {
  const T = templates || [...builtinTemplates(), ...USER_T];
  const n = strokes.length;
  const cand = T.filter((t) => t.n === n);
  if (!cand.length) return null;
  const b = bboxOf(strokes);
  const maxDim = Math.max(b.x1 - b.x0, b.y1 - b.y0);
  const coarse = cloud(strokes, NC), fine = cloud(strokes, NP);
  const feat = features(strokes), boxes = strokeBoxes(strokes);
  const scored = cand.map((t) => ({ t, f: featureDistance(feat, t.feat) + STRUCT_W * structureDistance(boxes, t.boxes) })).map((o) => ({ ...o, d: greedyMatch(coarse, o.t.coarse) + o.f }))
    .sort((p, q) => p.d - q.d);
  const short = scored.slice(0, SHORTLIST);
  const best = new Map();
  for (const { t, f } of short) {
    const cur = best.get(t.char);
    if (cur !== undefined && cur <= f) continue;
    const bound = cur !== undefined ? (cur - f) * NP : Infinity;
    const d = greedyMatch(fine, t.fine, bound) + f;
    if (cur === undefined || d < cur) best.set(t.char, d);
  }
  const ranked = [...best.entries()].map(([ch, d]) => ({
    char: ch,
    shape: d,
    dist: d + sizePenalty(ch, maxDim, em) + (PRIORS[ch] || 0) - (USER.some((u) => u.char === ch) ? 0.005 : 0),
  })).sort((p, q) => p.dist - q.dist);
  return { char: ranked[0].char, cost: ranked[0].dist, ranked, bbox: b, maxDim };
}

// distances -> probabilities, confidence and alternatives
function scoreOf(res) {
  // scale-free: p_c proportional to (d0 / d_c)^K, so a tie gives 0.5 and a runner-up at 1.5x the
  // winner's distance leaves the winner at ~0.92; DIST_FLOOR keeps near-perfect
  // matches from turning tiny absolute differences into certainty.
  const d0 = res.ranked[0].dist;
  const ws = res.ranked.map((r) => Math.pow((d0 + DIST_FLOOR) / (r.dist + DIST_FLOOR), POWER));
  const Z = ws.reduce((a, b) => a + b, 0);
  const probs = res.ranked.map((r, i) => ({ char: r.char, score: ws[i] / Z }));
  // absolute quality: a best match that is still far from every template is not trustworthy
  const q = d0 <= 0.1 ? 1 : Math.max(0.2, 1 - (d0 - 0.1) * 2.6);
  const confidence = probs[0].score * q;
  return { confidence, alternatives: probs.slice(1, 4).map((p) => ({ char: p.char, score: +p.score.toFixed(4) })), probs };
}

// ---------------------------------------------------------------------------------------------
function cleanStrokes(strokes) {
  const out = [];
  for (const s of strokes || []) {
    if (!Array.isArray(s)) continue;
    const pts = [];
    for (const p of s) {
      const x = Array.isArray(p) ? p[0] : p && p.x, y = Array.isArray(p) ? p[1] : p && p.y;
      if (!Number.isFinite(x) || !Number.isFinite(y)) continue;
      const last = pts[pts.length - 1];
      if (last && last.x === x && last.y === y) continue;
      pts.push({ x, y, t: p.t });
    }
    if (pts.length) out.push(pts);
  }
  return out;
}

function overlap1(a0, a1, b0, b1) { return Math.min(a1, b1) - Math.max(a0, b0); }

// Can strokes[i..j] plausibly be one symbol?  The strokes, linked whenever two of them overlap
// horizontally and sit close vertically, must form one connected cluster (order-free, so a "π"
// written leg, leg, bar still groups), and the cluster must not be huge.
function linked(a, b, em) {
  // strokes of one symbol cross or touch (x, +, 4, t, pi) or are stacked with strong
  // horizontal overlap (=, i, j, !, ÷, ≤). Whether a linked cluster really is one symbol is
  // decided by the match cost including the stroke-structure term.
  const pad = 0.04 * em;
  const ovx = overlap1(a.x0, a.x1, b.x0, b.x1), ovy = overlap1(a.y0, a.y1, b.y0, b.y1);
  const minW = Math.min(a.x1 - a.x0, b.x1 - b.x0), minH = Math.min(a.y1 - a.y0, b.y1 - b.y0);
  if (ovx >= -pad && ovy >= -pad && (ovx > 0 || ovy >= 0.5 * minH)) return true; // touching / crossing
  // stacked without touching: only when one part is a dot or a flat bar (i j ! ÷ = ≤ ≥)
  const vgap = Math.max(b.y0 - a.y1, a.y0 - b.y1);
  if (vgap > 0.4 * em) return false;
  const small = (q) => Math.max(q.x1 - q.x0, q.y1 - q.y0) < 0.22 * em;
  const flat = (q) => q.y1 - q.y0 < 0.45 * (q.x1 - q.x0);
  if (small(a) || small(b)) {
    // a dot may drift sideways (slanted handwriting): its centre within 0.25 em of the other part
    const d = small(a) ? a : b, o = small(a) ? b : a, c = (d.x0 + d.x1) / 2;
    return c >= o.x0 - 0.25 * em && c <= o.x1 + 0.25 * em;
  }
  return (flat(a) || flat(b)) && ovx + 2 * pad >= 0.6 * (minW + 2 * pad);
}
function plausible(boxes, i, j, em) {
  if (i === j) return true;
  const seen = new Set([i]), stack = [i];
  while (stack.length) {
    const a = stack.pop();
    for (let k = i; k <= j; k++) if (!seen.has(k) && linked(boxes[a], boxes[k], em)) { seen.add(k); stack.push(k); }
  }
  if (seen.size !== j - i + 1) return false;
  let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
  for (let k = i; k <= j; k++) { const b = boxes[k]; x0 = Math.min(x0, b.x0); y0 = Math.min(y0, b.y0); x1 = Math.max(x1, b.x1); y1 = Math.max(y1, b.y1); }
  return Math.max(x1 - x0, y1 - y0) < 3.2 * em;
}

function segment(strokes, em, templates) {
  const n = strokes.length;
  const boxes = strokes.map((s) => bboxOf([s]));
  const cache = new Map();
  const groupRes = (i, j) => {
    const key = i + ":" + j;
    if (!cache.has(key)) cache.set(key, plausible(boxes, i, j, em) ? classifyGroup(strokes.slice(i, j + 1), { em, templates }) : null);
    return cache.get(key);
  };
  // A flat stroke with substantial strokes both above and below inside its span is a fraction
  // bar: it is always a symbol of its own (otherwise "1 over bar" reads as a two-stroke "5").
  const isBar = boxes.map((b, k) => {
    const w = b.x1 - b.x0;
    if (!(w > 0.3 * em && b.y1 - b.y0 < 0.25 * w)) return false;
    const cyb = (b.y0 + b.y1) / 2;
    let up = false, down = false;
    boxes.forEach((o, m) => {
      if (m === k || Math.max(o.x1 - o.x0, o.y1 - o.y0) < 0.25 * em) return;
      const c = (o.x0 + o.x1) / 2;
      if (c < b.x0 || c > b.x1) return;
      // strictly separated from the bar (the base of a serif "1" touches its stem)
      if (o.y1 < b.y0 - 0.03 * em && cyb - o.y1 < 1.2 * em) up = true;
      if (o.y0 > b.y1 + 0.03 * em && o.y0 - cyb < 1.2 * em) down = true;
    });
    return up && down;
  });
  const best = new Array(n + 1).fill(Infinity), back = new Array(n + 1).fill(-1);
  best[0] = 0;
  for (let j = 1; j <= n; j++) {
    for (let k = 1; k <= 4 && k <= j; k++) {
      const i = j - k;
      if (best[i] === Infinity) continue;
      if (k > 1 && isBar.slice(i, j).some(Boolean)) continue;
      const r = groupRes(i, j - 1);
      if (!r) continue;
      const c = best[i] + r.cost + SYMBOL_PENALTY;
      if (c < best[j]) { best[j] = c; back[j] = i; }
    }
    if (best[j] === Infinity) { best[j] = best[j - 1] + 5; back[j] = j - 1; } // unknown stroke
  }
  const groups = [];
  for (let j = n; j > 0; j = back[j]) groups.push([back[j], j - 1]);
  groups.reverse();
  return groups.map(([i, j]) => ({ ids: Array.from({ length: j - i + 1 }, (_, k) => i + k), res: groupRes(i, j) }));
}

function guessEm(strokes) {
  const dims = strokes.map((s) => { const b = bboxOf([s]); return Math.max(b.x1 - b.x0, b.y1 - b.y0); }).filter((d) => d > 0).sort((a, b) => a - b);
  if (!dims.length) return 40;
  return Math.max(4, dims[dims.length >> 1] / 0.55);
}

// Two flat bars read as separate "-" but stacked (large horizontal overlap, a small vertical
// gap, nothing written between them) are an "=". Real minus signs sit side by side, and a
// fraction bar has content between it and anything below. The merged symbol is flagged as
// uncertain (confidence capped) so the reader confirms it.
function mergeStackedBars(symbols, em) {
  const cy = (r) => (r.y0 + r.y1) / 2;
  for (let i = 0; i < symbols.length; i++) {
    const a = symbols[i];
    if (a.char !== "-") continue;
    for (let j = i + 1; j < symbols.length; j++) {
      const b = symbols[j];
      if (b.char !== "-") continue;
      const A = a.bbox, B = b.bbox;
      const ov = Math.min(A.x1, B.x1) - Math.max(A.x0, B.x0);
      const gap = Math.abs(cy(B) - cy(A));
      if (ov < 0.5 * Math.min(A.x1 - A.x0, B.x1 - B.x0) || gap > 0.7 * em || gap < 0.08 * em) continue;
      const box = { x0: Math.min(A.x0, B.x0), y0: Math.min(A.y0, B.y0), x1: Math.max(A.x1, B.x1), y1: Math.max(A.y1, B.y1) };
      const cx = (r) => (r.x0 + r.x1) / 2;
      const between = symbols.some((c, k) => k !== i && k !== j && cx(c.bbox) > box.x0 && cx(c.bbox) < box.x1 && cy(c.bbox) > box.y0 && cy(c.bbox) < box.y1);
      if (between) continue;
      symbols[i] = {
        char: "=", confidence: Math.min(0.69, a.confidence, b.confidence),
        alternatives: [{ char: "=", score: 0.69 }, { char: "-", score: 0.31 }],
        bbox: box, strokeIds: [...(a.strokeIds || []), ...(b.strokeIds || [])],
      };
      symbols.splice(j, 1);
      break;
    }
  }
}

export function recognizeStrokes(input, opts = {}) {
  const strokes = cleanStrokes(input);
  const threshold = opts.threshold ?? LOW_CONFIDENCE;
  if (!strokes.length) return { text: "", symbols: [], lowConfidence: [], layout: null, em: null };
  const templates = [...builtinTemplates(), ...USER_T];
  let em = opts.em || guessEm(strokes);
  let groups = segment(strokes, em, templates);
  if (!opts.em) {
    // second pass with the text size implied by the first reading
    const first = groups.filter((g) => g.res).map((g) => ({ char: g.res.char, bbox: g.res.bbox, confidence: 1 }));
    const em2 = estimateEm(first, em);
    if (em2 && Number.isFinite(em2)) { em = em2; groups = segment(strokes, em, templates); }
  }
  const symbols = groups.map((g) => {
    if (!g.res) {
      const bbox = bboxOf(g.ids.map((i) => strokes[i]));
      return { char: "?", confidence: 0, alternatives: [], bbox, strokeIds: g.ids };
    }
    const sc = scoreOf(g.res);
    return {
      char: g.res.char,
      confidence: +sc.confidence.toFixed(4),
      alternatives: sc.alternatives,
      bbox: g.res.bbox,
      strokeIds: g.ids,
      distance: +g.res.cost.toFixed(4),
    };
  });
  contextRerank(symbols, { em });
  mergeStackedBars(symbols, em);
  const layout = analyzeLayout(symbols, { em });
  const lowConfidence = symbols.map((s, i) => (s.confidence < threshold ? i : -1)).filter((i) => i >= 0);
  return { text: layout.text, symbols, lowConfidence, layout, em };
}
