// Quelvra vision: offline recognition of printed math in photos and screenshots.
//
//   recognizeImage(imageData, { templates, threshold }) -> { text, symbols, lowConfidence, layout, ... }
//   buildFontTemplates(renderGlyph, opts) -> templates
//   browserFontRenderer(opts) -> renderGlyph (OffscreenCanvas + local fonts; browser only)
//
// imageData: ImageData-like { width, height, data: Uint8ClampedArray RGBA }.
// Pipeline: grayscale -> polarity check -> Sauvola binarization (integral images) -> deskew by
// projection-profile variance -> connected components -> speck removal -> per-component kNN
// classification on normalized features (zoning grid, projection histograms, aspect ratio,
// Hu moment invariants) -> size-aware re-scoring against the line's text size -> merging of
// multi-part glyphs (i j = ÷ ! ≤ ≥) -> radical detection -> shared 2D layout (layout.js).
// Templates are rendered at runtime from local fonts (browser) or the built-in pen font
// (raster.js); nothing is downloaded.

import { METRICS } from "./glyphs.js";
import { analyzeLayout, estimateEm, contextRerank } from "./layout.js";

export const LOW_CONFIDENCE = 0.7;
const GRID = 16;

// ---------------------------------------------------------------------------------------------
// Pixels
export function toGray(img) {
  const { width: W, height: H, data } = img;
  const g = new Float32Array(W * H);
  for (let i = 0, j = 0; i < g.length; i++, j += 4) {
    const a = data[j + 3] / 255;
    // transparent pixels count as paper
    g[i] = (0.299 * data[j] + 0.587 * data[j + 1] + 0.114 * data[j + 2]) * a + 255 * (1 - a);
  }
  return g;
}

function median(a) {
  if (!a.length) return NaN;
  const s = Float64Array.from(a).sort();
  const m = s.length >> 1;
  return s.length % 2 ? s[m] : (s[m - 1] + s[m]) / 2;
}

// Dark-mode screenshots (light ink on dark paper) are inverted first.
export function normalizePolarity(gray) {
  const sample = [];
  const step = Math.max(1, Math.floor(gray.length / 5000));
  for (let i = 0; i < gray.length; i += step) sample.push(gray[i]);
  const inverted = median(sample) < 110;
  if (inverted) for (let i = 0; i < gray.length; i++) gray[i] = 255 - gray[i];
  return inverted;
}

// Sauvola: T = m * (1 + k (s / R - 1)) over a w x w window, via integral images.
export function binarize(gray, W, H, { window = null, k = 0.34, R = 128 } = {}) {
  const w = window || Math.max(15, Math.min(61, Math.round(Math.max(W, H) / 16)) | 1);
  const r = w >> 1;
  const S = new Float64Array((W + 1) * (H + 1)), S2 = new Float64Array((W + 1) * (H + 1));
  for (let y = 0; y < H; y++) {
    let row = 0, row2 = 0;
    for (let x = 0; x < W; x++) {
      const v = gray[y * W + x];
      row += v; row2 += v * v;
      S[(y + 1) * (W + 1) + x + 1] = S[y * (W + 1) + x + 1] + row;
      S2[(y + 1) * (W + 1) + x + 1] = S2[y * (W + 1) + x + 1] + row2;
    }
  }
  const bin = new Uint8Array(W * H);
  for (let y = 0; y < H; y++) {
    const y0 = Math.max(0, y - r), y1 = Math.min(H, y + r + 1);
    for (let x = 0; x < W; x++) {
      const x0 = Math.max(0, x - r), x1 = Math.min(W, x + r + 1);
      const n = (x1 - x0) * (y1 - y0);
      const a = y1 * (W + 1), b = y0 * (W + 1);
      const sum = S[a + x1] - S[a + x0] - S[b + x1] + S[b + x0];
      const sum2 = S2[a + x1] - S2[a + x0] - S2[b + x1] + S2[b + x0];
      const m = sum / n, s = Math.sqrt(Math.max(0, sum2 / n - m * m));
      const T = m * (1 + k * (s / R - 1));
      const v = gray[y * W + x];
      bin[y * W + x] = v < T && v < 200 ? 1 : 0;
    }
  }
  return bin;
}

// Skew angle (degrees) by projection profile. Whole-ink profiles are nearly flat for a single
// short line of math, so the profile is taken over baseline anchors: the bottom-centre of every
// component of typical height. At the right angle the anchors of each text line fall into the
// same bins; the score is the sum of squared bin counts, with soft (two-bin) voting. The centre
// of the best plateau is returned; ties go to the smaller angle, and a line with fewer than
// four anchors is not deskewed at all.
export function estimateSkew(bin, W, H, { range = 10 } = {}) {
  const { comps } = connectedComponents(bin, W, H);
  const hs = comps.filter((c) => c.area >= 6).map((c) => c.y1 - c.y0);
  if (hs.length < 4) return 0;
  const medH = median(hs);
  const anchors = comps.filter((c) => c.area >= 6 && c.y1 - c.y0 > 0.45 * medH && c.y1 - c.y0 < 1.6 * medH)
    .map((c) => [(c.x0 + c.x1) / 2, c.y1]);
  if (anchors.length < 4) return 0;
  const tol = Math.max(1.5, 0.07 * medH);
  const score = (deg) => {
    // aligned pairs: sum of c(c-1) over bins, averaged over two bin phases
    const a = (deg * Math.PI) / 180, sn = Math.sin(a), cs = Math.cos(a);
    let q = 0;
    for (const off of [0, 0.5]) {
      const hist = new Map();
      for (const [x, y] of anchors) { const k = Math.floor((-x * sn + y * cs) / tol + off); hist.set(k, (hist.get(k) || 0) + 1); }
      for (const v of hist.values()) q += v * (v - 1);
    }
    return q / 2;
  };
  const angles = [];
  for (let d = -range; d <= range + 1e-9; d += 0.1) angles.push(+d.toFixed(2));
  const scores = angles.map(score);
  const best = Math.max(...scores);
  const s0 = score(0);
  // deskew only on clear evidence: at least two more aligned pairs than at 0 degrees
  if (anchors.length < 5 || best < Math.max(s0 * 1.3, s0 + 6)) return 0;
  const near = angles.filter((_, i) => scores[i] >= best * 0.97);
  // centre of the plateau containing the global best closest to zero
  near.sort((p, q) => Math.abs(p) - Math.abs(q));
  const seed = angles[scores.indexOf(best)];
  const plateau = near.filter((d) => Math.abs(d - seed) <= 2);
  return +(plateau.reduce((a, b) => a + b, 0) / plateau.length).toFixed(2);
}

// Rotate a binary image by -deg (undoing a measured skew of deg).
export function rotateBinary(bin, W, H, deg) {
  const a = (deg * Math.PI) / 180, c = Math.cos(a), s = Math.sin(a);
  const W2 = Math.ceil(Math.abs(W * c) + Math.abs(H * s)), H2 = Math.ceil(Math.abs(W * s) + Math.abs(H * c));
  const out = new Uint8Array(W2 * H2);
  const cx = W / 2, cy = H / 2, cx2 = W2 / 2, cy2 = H2 / 2;
  for (let y = 0; y < H2; y++) for (let x = 0; x < W2; x++) {
    const dx = x + 0.5 - cx2, dy = y + 0.5 - cy2;
    // inverse map: source = R(+deg) * dest, so dest = R(-deg) * source
    const sx = Math.round(c * dx - s * dy + cx - 0.5), sy = Math.round(s * dx + c * dy + cy - 0.5);
    if (sx >= 0 && sy >= 0 && sx < W && sy < H) out[y * W2 + x] = bin[sy * W + sx];
  }
  return { bin: out, W: W2, H: H2 };
}

// 8-connected components.
export function connectedComponents(bin, W, H) {
  const label = new Int32Array(W * H).fill(-1);
  const comps = [];
  const stack = new Int32Array(W * H);
  for (let i = 0; i < W * H; i++) {
    if (!bin[i] || label[i] >= 0) continue;
    const id = comps.length;
    let sp = 0, x0 = W, y0 = H, x1 = -1, y1 = -1, area = 0;
    const pix = [];
    stack[sp++] = i; label[i] = id;
    while (sp) {
      const p = stack[--sp];
      const x = p % W, y = (p - x) / W;
      pix.push(p); area++;
      if (x < x0) x0 = x; if (x > x1) x1 = x; if (y < y0) y0 = y; if (y > y1) y1 = y;
      for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) {
        const xx = x + dx, yy = y + dy;
        if (xx < 0 || yy < 0 || xx >= W || yy >= H) continue;
        const q = yy * W + xx;
        if (bin[q] && label[q] < 0) { label[q] = id; stack[sp++] = q; }
      }
    }
    comps.push({ id, x0, y0, x1: x1 + 1, y1: y1 + 1, area, pix });
  }
  return { comps, label, W, H };
}

// ---------------------------------------------------------------------------------------------
// Features
function maskOf(parts, W) {
  let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
  for (const c of parts) { x0 = Math.min(x0, c.x0); y0 = Math.min(y0, c.y0); x1 = Math.max(x1, c.x1); y1 = Math.max(y1, c.y1); }
  const w = x1 - x0, h = y1 - y0;
  const m = new Uint8Array(w * h);
  for (const c of parts) for (const p of c.pix) { const x = p % W, y = (p - x) / W; m[(y - y0) * w + (x - x0)] = 1; }
  return { m, w, h, x0, y0 };
}

function huMoments(m, w, h) {
  let m00 = 0, m10 = 0, m01 = 0;
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) if (m[y * w + x]) { m00++; m10 += x; m01 += y; }
  if (!m00) return [0, 0, 0, 0];
  const xc = m10 / m00, yc = m01 / m00;
  let mu20 = 0, mu02 = 0, mu11 = 0, mu30 = 0, mu03 = 0, mu21 = 0, mu12 = 0;
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) if (m[y * w + x]) {
    const dx = x - xc, dy = y - yc;
    mu20 += dx * dx; mu02 += dy * dy; mu11 += dx * dy;
    mu30 += dx * dx * dx; mu03 += dy * dy * dy; mu21 += dx * dx * dy; mu12 += dx * dy * dy;
  }
  const n = (mu, p, q) => mu / Math.pow(m00, 1 + (p + q) / 2);
  const e20 = n(mu20, 2, 0), e02 = n(mu02, 0, 2), e11 = n(mu11, 1, 1);
  const e30 = n(mu30, 3, 0), e03 = n(mu03, 0, 3), e21 = n(mu21, 2, 1), e12 = n(mu12, 1, 2);
  const h1 = e20 + e02;
  const h2 = (e20 - e02) ** 2 + 4 * e11 * e11;
  const h3 = (e30 - 3 * e12) ** 2 + (3 * e21 - e03) ** 2;
  const h4 = (e30 + e12) ** 2 + (e21 + e03) ** 2;
  const lg = (v) => (v > 0 ? Math.max(-12, Math.log10(v)) : -12);
  return [lg(h1), lg(h2), lg(h3), lg(h4)];
}

// Feature vector of a binary mask (w x h).
export function glyphFeatures(m, w, h) {
  const g = new Float32Array(GRID * GRID);
  const s = GRID / Math.max(w, h);
  const ox = (GRID - w * s) / 2, oy = (GRID - h * s) / 2;
  const SS = 4;
  for (let gy = 0; gy < GRID; gy++) for (let gx = 0; gx < GRID; gx++) {
    let hit = 0;
    for (let sy = 0; sy < SS; sy++) for (let sx = 0; sx < SS; sx++) {
      const x = Math.floor((gx + (sx + 0.5) / SS - ox) / s), y = Math.floor((gy + (sy + 0.5) / SS - oy) / s);
      if (x >= 0 && y >= 0 && x < w && y < h && m[y * w + x]) hit++;
    }
    g[gy * GRID + gx] = hit / (SS * SS);
  }
  const f = [];
  const Z = GRID / 8;
  for (let zy = 0; zy < 8; zy++) for (let zx = 0; zx < 8; zx++) {
    let t = 0;
    for (let y = 0; y < Z; y++) for (let x = 0; x < Z; x++) t += g[(zy * Z + y) * GRID + zx * Z + x];
    f.push(t / (Z * Z));
  }
  for (let y = 0; y < GRID; y++) { let t = 0; for (let x = 0; x < GRID; x++) t += g[y * GRID + x]; f.push((0.5 * t) / GRID); }
  for (let x = 0; x < GRID; x++) { let t = 0; for (let y = 0; y < GRID; y++) t += g[y * GRID + x]; f.push((0.5 * t) / GRID); }
  f.push(0.6 * Math.max(-3, Math.min(3, Math.log((w + 1) / (h + 1)))));
  for (const v of huMoments(m, w, h)) f.push(0.04 * v);
  return Float32Array.from(f);
}

function dist2(a, b) {
  let d = 0;
  for (let i = 0; i < a.length; i++) { const t = a[i] - b[i]; d += t * t; }
  return Math.sqrt(d);
}

// ---------------------------------------------------------------------------------------------
// Templates
const PART_OF = { i: "ı", j: "ȷ" };
const SKIP_MULTI = new Set(["=", "÷", "≤", "≥", "!"]);

// renderGlyph(char, fontSpec) -> ImageData-like (dark glyph on light paper) or null.
// fontSpec is passed through untouched; `size` (px per em) must be present so symbol sizes can
// be related to the text size.
export function buildFontTemplates(renderGlyph, { chars = Object.keys(METRICS), fonts = null, sizes = [32, 48] } = {}) {
  const fontList = fonts || [{ family: "sans-serif" }, { family: "serif" }, { family: "monospace" }, { family: "serif", style: "italic" }];
  const out = [];
  for (const ch of chars) {
    for (const f of fontList) for (const size of sizes) {
      const spec = { ...f, size };
      let img;
      try { img = renderGlyph(ch, spec); } catch (_) { img = null; }
      if (!img || !img.width) continue;
      const g = toGray(img);
      const bin = new Uint8Array(g.length);
      for (let i = 0; i < g.length; i++) bin[i] = g[i] < 128 ? 1 : 0;
      const { comps } = connectedComponents(bin, img.width, img.height);
      const real = comps.filter((c) => c.area >= 2);
      if (!real.length) continue;
      let label = ch, parts = real;
      if (real.length > 1) {
        if (PART_OF[ch]) { label = PART_OF[ch]; parts = [real.reduce((a, b) => (b.area > a.area ? b : a))]; }
        else if (SKIP_MULTI.has(ch)) continue;
        else parts = real; // e.g. a broken glyph: keep as a whole
      } else if (SKIP_MULTI.has(ch) && ch !== "!") {
        // single-component rendering of a normally multi-part glyph (ligature fonts): keep
      }
      const { m, w, h } = maskOf(parts, img.width);
      out.push({ char: label, feat: glyphFeatures(m, w, h), size: Math.max(w, h) / size, font: f.family + (f.style ? " " + f.style : "") });
    }
  }
  return out;
}

// A user-taught photo template: the ink of `img` (all of it, as one glyph). emPx is the text
// size (px per em) the sample was written or cropped at, used for size plausibility.
export function templateFromImage(char, img, emPx = null) {
  const g = toGray(img);
  normalizePolarity(g);
  const bin = binarize(g, img.width, img.height);
  const { comps } = connectedComponents(bin, img.width, img.height);
  const parts = comps.filter((c) => c.area >= 3);
  if (!parts.length) throw new Error("templateFromImage: no ink found");
  const { m, w, h } = maskOf(parts, img.width);
  return { char, feat: glyphFeatures(m, w, h), size: emPx ? Math.max(w, h) / emPx : null, font: "user", user: true };
}

// Browser helper: glyph renderer backed by OffscreenCanvas and the fonts installed locally.
export function browserFontRenderer() {
  const OC = globalThis.OffscreenCanvas;
  if (!OC) return null;
  return (ch, spec) => {
    const size = spec.size || 48;
    const W = Math.ceil(size * 2.2), H = Math.ceil(size * 2.2);
    const cv = new OC(W, H);
    const ctx = cv.getContext("2d", { willReadFrequently: true });
    ctx.fillStyle = "#fff";
    ctx.fillRect(0, 0, W, H);
    ctx.fillStyle = "#000";
    ctx.textBaseline = "alphabetic";
    ctx.font = `${spec.style || ""} ${spec.weight || ""} ${size}px ${spec.family || "sans-serif"}`.trim();
    ctx.fillText(ch, size * 0.4, size * 1.45);
    return ctx.getImageData(0, 0, W, H);
  };
}

// ---------------------------------------------------------------------------------------------
// Classification
function sizePenalty(ch, maxDim, em) {
  const base = ch === "ı" ? "i" : ch === "ȷ" ? "j" : ch;
  const m = METRICS[base];
  if (!m || !em) return 0;
  const s = maxDim / em;
  const lo = m.size[0] * 0.55, hi = m.size[1] * 1.4;
  let r = 0;
  if (s < lo) r = Math.log(Math.max(s, 0.01) / lo);
  else if (s > hi) r = Math.log(s / hi);
  return 0.35 * r * r + 0.15 * Math.abs(r);
}

function classify(feat, maxDim, templates, em, k = 7) {
  const perClass = new Map();
  for (const t of templates) {
    const d = dist2(feat, t.feat);
    const cur = perClass.get(t.char);
    if (!cur) perClass.set(t.char, [d]);
    else if (cur.length < k) cur.push(d);
    else { let mi = 0; for (let i = 1; i < cur.length; i++) if (cur[i] > cur[mi]) mi = i; if (d < cur[mi]) cur[mi] = d; }
  }
  const ranked = [...perClass.entries()].map(([ch, ds]) => {
    ds.sort((a, b) => a - b);
    const d = ds.length > 1 ? 0.7 * ds[0] + 0.3 * ds[1] : ds[0];
    return { char: ch, shape: d, dist: d + sizePenalty(ch, maxDim, em) };
  }).sort((a, b) => a.dist - b.dist);
  return ranked;
}

// Scale-free confidence. Class probabilities follow a power law of the per-class distances
// (p_c proportional to d_c^-K), so a tie between two classes gives 0.5 each and a clear winner at 70% of
// the runner-up's distance gets about 0.97. The absolute yardstick for "unlike every template"
// is the median distance between neighbouring templates of DIFFERENT classes.
const SCALES = new WeakMap();
function templateScale(templates) {
  if (SCALES.has(templates)) return SCALES.get(templates);
  const ds = [];
  const step = Math.max(1, Math.floor(templates.length / 300));
  for (let i = 0; i < templates.length; i += step) {
    const a = templates[i];
    let best = Infinity;
    for (const b of templates) if (b.char !== a.char) { const d = dist2(a.feat, b.feat); if (d < best) best = d; }
    if (Number.isFinite(best)) ds.push(best);
  }
  const m = ds.length ? median(ds) : 1;
  SCALES.set(templates, m);
  return m;
}

const K = 10;
function scoreRanked(ranked, scale) {
  const d0 = Math.max(1e-6, ranked[0].dist);
  const ws = ranked.map((r) => Math.pow(d0 / Math.max(1e-6, r.dist), K));
  const Z = ws.reduce((a, b) => a + b, 0);
  const probs = ranked.map((r, i) => ({ char: r.char, score: ws[i] / Z }));
  const u = ranked[0].shape / scale;
  const q = u <= 1.5 ? 1 : Math.max(0.2, 1 - (u - 1.5) * 0.5);
  return { confidence: probs[0].score * q, probs };
}

// A radical sign printed with its overbar: wide component whose top band is a long horizontal
// run on the right and whose left part is a V reaching the bottom.
function looksLikeRadical(c, W) {
  const w = c.x1 - c.x0, h = c.y1 - c.y0;
  if (w < 1.2 * h || h < 8) return false;
  const { m } = maskOf([c], W);
  const band = Math.max(2, Math.round(0.14 * h));
  let topRun = 0;
  const from = Math.round(0.45 * w);
  for (let x = from; x < w; x++) { let hit = 0; for (let y = 0; y < band; y++) hit |= m[y * w + x]; topRun += hit; }
  if (topRun < 0.9 * (w - from)) return false;
  // under the bar on the right, the component itself is empty
  let under = 0, tot = 0;
  for (let y = Math.round(0.35 * h); y < h; y++) for (let x = from; x < w; x++) { tot++; under += m[y * w + x]; }
  if (under > 0.03 * tot) return false;
  // the V: ink in the bottom quarter within the left 45%
  let low = 0;
  for (let y = Math.round(0.75 * h); y < h; y++) for (let x = 0; x < Math.round(0.45 * w); x++) low += m[y * w + x];
  return low > 0;
}

// ---------------------------------------------------------------------------------------------
// Merging of multi-part glyphs
const STEMS = new Set(["ı", "1", "l", "|", "ȷ", "/", ")", "("]);
function box(g) { return { x0: g.x0, y0: g.y0, x1: g.x1, y1: g.y1 }; }
function xOverlap(a, b) { return Math.min(a.x1, b.x1) - Math.max(a.x0, b.x0); }
function isDot(g, em) {
  const w = g.x1 - g.x0, h = g.y1 - g.y0;
  return (g.char === "." || (Math.max(w, h) < 0.2 * em && w < 2 * h && h < 2 * w)) && Math.max(w, h) < 0.25 * em;
}
function isBar(g) { return g.char === "-" || g.char === "−"; }
function top3(g) { return [g.char, ...g.alternatives.map((a) => a.char)].slice(0, 3); }

function mergeParts(glyphs, em) {
  const used = new Set();
  const out = [];
  const combine = (parts, char, alternatives = []) => {
    parts.forEach((p) => used.add(p));
    const conf = Math.min(...parts.map((p) => p.confidence));
    out.push({
      char, confidence: conf, alternatives,
      x0: Math.min(...parts.map((p) => p.x0)), y0: Math.min(...parts.map((p) => p.y0)),
      x1: Math.max(...parts.map((p) => p.x1)), y1: Math.max(...parts.map((p) => p.y1)),
      comps: parts.flatMap((p) => p.comps), parts: parts.map((p) => p.char),
    });
  };
  const byX = [...glyphs].sort((a, b) => a.x0 - b.x0);
  // bars first: ÷, =, ≤, ≥
  for (const b of byX) {
    if (used.has(b) || !isBar(b)) continue;
    const bw = b.x1 - b.x0;
    const near = byX.filter((o) => o !== b && !used.has(o) && xOverlap(o, b) > 0.3 * Math.min(bw, o.x1 - o.x0));
    const dots = near.filter((o) => isDot(o, em) && Math.min(Math.abs(o.y1 - b.y0), Math.abs(o.y0 - b.y1)) < 0.45 * em);
    const up = dots.find((o) => o.y1 <= b.y0), dn = dots.find((o) => o.y0 >= b.y1);
    if (up && dn && bw < 1.2 * em) { combine([b, up, dn], "÷", [{ char: "+", score: 0.01 }]); continue; }
    const twin = near.find((o) => isBar(o) && Math.abs((o.x1 - o.x0) - bw) < 0.4 * bw && xOverlap(o, b) > 0.6 * bw && Math.abs((o.y0 + o.y1) / 2 - (b.y0 + b.y1) / 2) < Math.max(0.5 * em, 0.8 * bw) && Math.abs((o.y0 + o.y1) / 2 - (b.y0 + b.y1) / 2) > 0);
    if (twin) {
      // Only an "=" if nothing sits between/around like a fraction (fractions have wider bars
      // with content above and below; "=" bars are short and similar).
      if (bw < 1.1 * em) { combine([b, twin], "=", [{ char: "-", score: 0.01 }]); continue; }
    }
    const chev = near.find((o) => (o.char === "<" || o.char === ">") && o.y1 <= b.y0 + 0.05 * em && b.y0 - o.y1 < 0.35 * em);
    if (chev) { combine([b, chev], chev.char === "<" ? "≤" : "≥", [{ char: chev.char, score: 0.02 }]); continue; }
  }
  // dots with stems: i, j, !
  for (const d of byX) {
    if (used.has(d) || !isDot(d, em)) continue;
    const cands = byX.filter((o) => o !== d && !used.has(o) && !isDot(o, em) && top3(o).some((c) => STEMS.has(c)) && (o.x1 - o.x0) < 0.45 * em);
    const cxd = (d.x0 + d.x1) / 2;
    const under = cands.find((o) => cxd >= o.x0 - 0.12 * em && cxd <= o.x1 + 0.12 * em && o.y0 >= d.y1 - 0.02 * em && o.y0 - d.y1 < 0.4 * em);
    if (under) {
      const isJ = top3(under).includes("ȷ") && !top3(under).includes("ı") || under.char === "ȷ";
      combine([d, under], isJ ? "j" : "i", [{ char: isJ ? "i" : "j", score: 0.05 }]);
      continue;
    }
    const over = cands.find((o) => cxd >= o.x0 - 0.12 * em && cxd <= o.x1 + 0.12 * em && d.y0 >= o.y1 - 0.02 * em && d.y0 - o.y1 < 0.35 * em && (o.y1 - o.y0) > 0.45 * em);
    if (over) { combine([over, d], "!", [{ char: "i", score: 0.02 }]); continue; }
  }
  for (const g of glyphs) if (!used.has(g)) {
    if (g.char === "ı" || g.char === "ȷ") {
      // a dotless stem whose dot was lost: say so through a low confidence
      const alt = g.char === "ı" ? "i" : "j";
      out.push({ ...g, char: alt, confidence: Math.min(g.confidence, 0.4), alternatives: [{ char: "1", score: 0.3 }, ...g.alternatives.filter((a) => a.char !== alt)].slice(0, 3) });
    } else out.push(g);
  }
  return out;
}

// ---------------------------------------------------------------------------------------------
export function recognizeImage(img, opts = {}) {
  const threshold = opts.threshold ?? LOW_CONFIDENCE;
  const templates = opts.templates;
  if (!templates || !templates.length) throw new Error("recognizeImage needs templates (buildFontTemplates)");
  if (!img || !img.width || !img.height || !img.data) throw new Error("recognizeImage needs an ImageData-like {width, height, data}");
  const t0 = Date.now();
  let W = img.width, H = img.height;
  const gray = toGray(img);
  const inverted = normalizePolarity(gray);
  let bin = binarize(gray, W, H, opts.binarize || {});
  const skew = opts.deskew === false ? 0 : estimateSkew(bin, W, H);
  if (Math.abs(skew) >= 0.3) ({ bin, W, H } = rotateBinary(bin, W, H, skew));
  const { comps } = connectedComponents(bin, W, H);
  // speck removal relative to the typical component height
  const big = comps.filter((c) => c.area >= 6).map((c) => c.y1 - c.y0);
  const medH = big.length ? median(big) : 10;
  const minArea = Math.max(4, 0.012 * medH * medH);
  const kept = comps.filter((c) => c.area >= minArea);
  const warnings = [];
  if (kept.length > 400) warnings.push("Very many ink blobs: the photo may be too noisy or contain more than math.");
  // first pass: shape only
  const glyphs = kept.map((c) => {
    const { m, w, h } = maskOf([c], W);
    const feat = glyphFeatures(m, w, h);
    return { x0: c.x0, y0: c.y0, x1: c.x1, y1: c.y1, feat, maxDim: Math.max(w, h), comps: [c.id], radical: looksLikeRadical(c, W) };
  });
  const scale = templateScale(templates);
  const classifyAll = (em) => {
    for (const g of glyphs) {
      if (g.radical) { g.char = "√"; g.confidence = 0.9; g.alternatives = []; continue; }
      const ranked = classify(g.feat, g.maxDim, templates, em);
      const sc = scoreRanked(ranked, scale);
      g.char = ranked[0].char;
      g.confidence = sc.confidence;
      g.alternatives = sc.probs.slice(1, 4).map((p) => ({ char: p.char, score: +p.score.toFixed(4) }));
    }
  };
  classifyAll(opts.em || null);
  let em = opts.em || estimateEm(glyphs.filter((g) => METRICS[g.char]).map((g) => ({ char: g.char, bbox: box(g), confidence: g.confidence })));
  if (!opts.em && Number.isFinite(em)) classifyAll(em);
  const merged = mergeParts(glyphs, em);
  const symbols = merged.map((g) => ({
    char: g.char,
    confidence: +Math.max(0, Math.min(1, g.confidence)).toFixed(4),
    alternatives: g.alternatives,
    bbox: { x0: g.x0, y0: g.y0, x1: g.x1, y1: g.y1 },
    components: g.comps,
    ...(g.parts ? { parts: g.parts } : {}),
  }));
  symbols.sort((a, b) => a.bbox.x0 - b.bbox.x0);
  contextRerank(symbols, { em });
  const layout = analyzeLayout(symbols, { em });
  const lowConfidence = symbols.map((s, i) => (s.confidence < threshold ? i : -1)).filter((i) => i >= 0);
  return {
    text: layout.text, symbols, lowConfidence, layout, em,
    preprocess: { skew, inverted, width: W, height: H, components: comps.length, kept: kept.length },
    warnings, ms: Date.now() - t0,
  };
}
