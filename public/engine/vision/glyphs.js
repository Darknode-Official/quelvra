// Quelvra vision: procedural glyph geometry.
//
// Every symbol the recogniser knows is described here as one or more pen-stroke VARIANTS in
// em units (x to the right, y UP, baseline at y = 0, digit height 0.7, x-height 0.5). The same
// geometry feeds three consumers:
//   * strokes.js turns variants into $P point-cloud templates (with synthetic jitter copies),
//   * raster.js draws them with a thick pen to make "font" bitmaps for photo templates and tests,
//   * typeset() lays out small expressions so tests can synthesize handwriting and images.
// Nothing here is downloaded or learned; it is all written by hand as code.

const STEP = 0.02;

function dist(a, b) { return Math.hypot(b[0] - a[0], b[1] - a[1]); }

// Straight polyline through the given points, sampled every STEP em.
export function L(...pts) {
  const out = [pts[0]];
  for (let i = 1; i < pts.length; i++) {
    const a = pts[i - 1], b = pts[i];
    const n = Math.max(1, Math.ceil(dist(a, b) / STEP));
    for (let k = 1; k <= n; k++) out.push([a[0] + ((b[0] - a[0]) * k) / n, a[1] + ((b[1] - a[1]) * k) / n]);
  }
  return out;
}
// Elliptic arc from angle a0 to a1 (degrees, counter-clockwise positive, y up).
export function A(cx, cy, rx, ry, a0, a1) {
  const len = (Math.abs(a1 - a0) * Math.PI / 180) * Math.max(rx, ry);
  const n = Math.max(2, Math.ceil(len / STEP));
  const out = [];
  for (let k = 0; k <= n; k++) {
    const t = ((a0 + ((a1 - a0) * k) / n) * Math.PI) / 180;
    out.push([cx + rx * Math.cos(t), cy + ry * Math.sin(t)]);
  }
  return out;
}
// Cubic Bezier.
export function C(p0, p1, p2, p3) {
  const len = dist(p0, p1) + dist(p1, p2) + dist(p2, p3);
  const n = Math.max(2, Math.ceil(len / STEP));
  const out = [];
  for (let k = 0; k <= n; k++) {
    const t = k / n, u = 1 - t;
    out.push([
      u * u * u * p0[0] + 3 * u * u * t * p1[0] + 3 * u * t * t * p2[0] + t * t * t * p3[0],
      u * u * u * p0[1] + 3 * u * u * t * p1[1] + 3 * u * t * t * p2[1] + t * t * t * p3[1],
    ]);
  }
  return out;
}
// Join several pieces into one continuous stroke (drops duplicated joints).
export function J(...parts) {
  const out = [];
  for (const p of parts) for (const q of p) {
    const last = out[out.length - 1];
    if (!last || dist(last, q) > 1e-9) out.push(q);
  }
  return out;
}
const dot = (x, y, r = 0.035) => A(x, y, r, r, 0, 360);

// ---------------------------------------------------------------------------------------------
// Symbol metrics (em units, y up). lo/hi: natural vertical extent. size: [min,max] of the natural
// largest dimension (used for size-aware rescoring). kind: "letter" | "digit" | "op" | "flat" |
// "open" | "close" | "big" | "dot". flat symbols do not tell the text size.
export const METRICS = {
  0: { lo: 0, hi: 0.7, size: [0.6, 0.8], kind: "digit" },
  1: { lo: 0, hi: 0.7, size: [0.6, 0.8], kind: "digit" },
  2: { lo: 0, hi: 0.7, size: [0.6, 0.8], kind: "digit" },
  3: { lo: 0, hi: 0.7, size: [0.6, 0.8], kind: "digit" },
  4: { lo: 0, hi: 0.7, size: [0.6, 0.8], kind: "digit" },
  5: { lo: 0, hi: 0.7, size: [0.6, 0.8], kind: "digit" },
  6: { lo: 0, hi: 0.7, size: [0.6, 0.8], kind: "digit" },
  7: { lo: 0, hi: 0.7, size: [0.6, 0.8], kind: "digit" },
  8: { lo: 0, hi: 0.7, size: [0.6, 0.8], kind: "digit" },
  9: { lo: 0, hi: 0.7, size: [0.6, 0.8], kind: "digit" },
  x: { lo: 0, hi: 0.5, size: [0.4, 0.6], kind: "letter" },
  y: { lo: -0.22, hi: 0.5, size: [0.6, 0.8], kind: "letter" },
  z: { lo: 0, hi: 0.5, size: [0.4, 0.6], kind: "letter" },
  a: { lo: 0, hi: 0.5, size: [0.4, 0.6], kind: "letter" },
  b: { lo: 0, hi: 0.75, size: [0.65, 0.85], kind: "letter" },
  c: { lo: 0, hi: 0.5, size: [0.4, 0.6], kind: "letter" },
  d: { lo: 0, hi: 0.75, size: [0.65, 0.85], kind: "letter" },
  e: { lo: 0, hi: 0.5, size: [0.4, 0.6], kind: "letter" },
  n: { lo: 0, hi: 0.5, size: [0.4, 0.6], kind: "letter" },
  t: { lo: 0, hi: 0.72, size: [0.6, 0.8], kind: "letter" },
  i: { lo: 0, hi: 0.72, size: [0.6, 0.8], kind: "letter" },
  j: { lo: -0.22, hi: 0.72, size: [0.8, 1.0], kind: "letter" },
  l: { lo: 0, hi: 0.75, size: [0.65, 0.85], kind: "letter" },
  "π": { lo: 0, hi: 0.5, size: [0.45, 0.6], kind: "letter" },
  "θ": { lo: 0, hi: 0.72, size: [0.6, 0.8], kind: "letter" },
  "+": { lo: 0.05, hi: 0.53, size: [0.35, 0.55], kind: "op" },
  "-": { lo: 0.27, hi: 0.31, size: [0.3, 12], kind: "flat" },
  "=": { lo: 0.17, hi: 0.41, size: [0.35, 0.6], kind: "flat" },
  "<": { lo: 0.02, hi: 0.52, size: [0.4, 0.6], kind: "op" },
  ">": { lo: 0.02, hi: 0.52, size: [0.4, 0.6], kind: "op" },
  "≤": { lo: 0, hi: 0.6, size: [0.5, 0.7], kind: "op" },
  "≥": { lo: 0, hi: 0.6, size: [0.5, 0.7], kind: "op" },
  "÷": { lo: 0.05, hi: 0.55, size: [0.4, 0.6], kind: "op" },
  "/": { lo: -0.1, hi: 0.8, size: [0.75, 1.0], kind: "op" },
  "^": { lo: 0.45, hi: 0.75, size: [0.3, 0.5], kind: "flat" },
  "(": { lo: -0.2, hi: 0.8, size: [0.85, 1.15], kind: "open" },
  ")": { lo: -0.2, hi: 0.8, size: [0.85, 1.15], kind: "close" },
  "|": { lo: -0.2, hi: 0.8, size: [0.85, 1.15], kind: "op" },
  "!": { lo: 0, hi: 0.72, size: [0.6, 0.8], kind: "op" },
  ".": { lo: 0, hi: 0.07, size: [0, 0.14], kind: "dot" },
  ",": { lo: -0.14, hi: 0.07, size: [0.12, 0.3], kind: "dot" },
  "√": { lo: -0.05, hi: 0.8, size: [0.7, 12], kind: "big" },
  "∫": { lo: -0.25, hi: 0.95, size: [1.0, 2.5], kind: "big" },
};
export const SYMBOLS = Object.keys(METRICS);

// ---------------------------------------------------------------------------------------------
// Variants. Each entry: { name, strokes: [[ [x,y], ... ], ...] }.
function sqrtStroke(bar) {
  return J(L([0, 0.32], [0.08, 0.37], [0.2, 0], [0.34, 0.8], [0.34 + bar, 0.8]));
}
export function radical(width, lo, hi) {
  // A radical sign covering [lo, hi] vertically with an overbar of the given width (em units).
  const h = hi - lo;
  const hook = Math.min(0.45, 0.25 + 0.12 * h);
  return [J(L([0, lo + 0.4 * h], [hook * 0.25, lo + 0.46 * h], [hook * 0.6, lo], [hook, hi], [hook + width, hi]))];
}

export const VARIANTS = {
  0: [
    { name: "oval", strokes: [A(0.25, 0.35, 0.21, 0.35, 90, 450)] },
    { name: "oval-cw", strokes: [A(0.25, 0.35, 0.2, 0.35, 100, -250)] },
    { name: "narrow", strokes: [A(0.22, 0.35, 0.16, 0.35, 80, 440)] },
  ],
  1: [
    { name: "flag", strokes: [L([0.08, 0.52], [0.26, 0.7], [0.26, 0])] },
    { name: "stem", strokes: [L([0.25, 0.7], [0.25, 0])] },
    { name: "flag-base", strokes: [L([0.08, 0.52], [0.26, 0.7], [0.26, 0]), L([0.08, 0], [0.44, 0])] },
  ],
  2: [
    { name: "curve", strokes: [J(A(0.24, 0.5, 0.2, 0.19, 160, -30), L([0.41, 0.4], [0.03, 0], [0.47, 0]))] },
    { name: "swan", strokes: [J(C([0.04, 0.55], [0.1, 0.78], [0.5, 0.75], [0.4, 0.45]), C([0.4, 0.45], [0.3, 0.25], [0.1, 0.1], [0.03, 0]), L([0.03, 0], [0.47, 0.02]))] },
    { name: "loop", strokes: [J(A(0.24, 0.5, 0.2, 0.19, 160, -30), L([0.41, 0.4], [0.05, 0.03]), A(0.1, 0.07, 0.06, 0.05, 220, -60), L([0.13, 0.03], [0.47, 0]))] },
  ],
  3: [
    { name: "round", strokes: [J(A(0.24, 0.53, 0.18, 0.17, 150, -90), A(0.24, 0.19, 0.2, 0.19, 90, -150))] },
    { name: "flat-top", strokes: [J(L([0.05, 0.7], [0.43, 0.7], [0.2, 0.42]), A(0.24, 0.2, 0.2, 0.21, 70, -150))] },
    { name: "cusp", strokes: [J(C([0.05, 0.62], [0.2, 0.78], [0.5, 0.7], [0.18, 0.37]), C([0.18, 0.37], [0.6, 0.35], [0.5, -0.1], [0.03, 0.08]))] },
  ],
  4: [
    { name: "closed", strokes: [L([0.36, 0], [0.36, 0.7], [0.02, 0.2], [0.48, 0.2])] },
    { name: "open", strokes: [L([0.24, 0.7], [0.04, 0.25], [0.48, 0.25]), L([0.36, 0.55], [0.36, 0])] },
    { name: "open-long", strokes: [L([0.16, 0.7], [0.04, 0.28], [0.48, 0.28]), L([0.37, 0.7], [0.37, 0])] },
  ],
  5: [
    { name: "two-stroke", strokes: [J(L([0.12, 0.7], [0.08, 0.4]), A(0.24, 0.23, 0.21, 0.22, 130, -150)), L([0.12, 0.7], [0.44, 0.7])] },
    { name: "one-stroke", strokes: [J(L([0.44, 0.7], [0.12, 0.7], [0.08, 0.4]), A(0.24, 0.23, 0.21, 0.22, 130, -150))] },
  ],
  6: [
    { name: "loop", strokes: [J(C([0.4, 0.68], [0.15, 0.7], [0.03, 0.4], [0.05, 0.2]), A(0.25, 0.2, 0.2, 0.2, 180, 540))] },
    { name: "straight", strokes: [J(L([0.36, 0.7], [0.07, 0.25]), A(0.25, 0.2, 0.2, 0.2, 165, 525))] },
  ],
  7: [
    { name: "plain", strokes: [L([0.03, 0.7], [0.47, 0.7], [0.17, 0])] },
    { name: "crossed", strokes: [L([0.03, 0.7], [0.47, 0.7], [0.17, 0]), L([0.14, 0.36], [0.42, 0.36])] },
  ],
  8: [
    { name: "one-stroke", strokes: [J(A(0.25, 0.53, 0.16, 0.17, -90, 270), A(0.25, 0.19, 0.2, 0.19, 90, -270))] },
    { name: "s-cross", strokes: [J(C([0.4, 0.62], [0.3, 0.8], [0.02, 0.7], [0.1, 0.5]), C([0.1, 0.5], [0.2, 0.35], [0.5, 0.3], [0.45, 0.12]), C([0.45, 0.12], [0.4, -0.05], [0.05, -0.05], [0.06, 0.15]), C([0.06, 0.15], [0.08, 0.3], [0.4, 0.4], [0.42, 0.56]), C([0.42, 0.56], [0.42, 0.66], [0.38, 0.7], [0.3, 0.7]))] },
    { name: "two-circles", strokes: [A(0.25, 0.53, 0.16, 0.17, -90, 270), A(0.25, 0.19, 0.2, 0.19, 90, 450)] },
  ],
  9: [
    { name: "straight", strokes: [J(A(0.23, 0.5, 0.19, 0.19, -10, 350), L([0.42, 0.47], [0.4, 0]))] },
    { name: "curved", strokes: [J(A(0.23, 0.5, 0.19, 0.19, -10, 350), C([0.42, 0.47], [0.43, 0.2], [0.35, 0], [0.1, 0.02]))] },
    { name: "two-stroke", strokes: [A(0.23, 0.5, 0.19, 0.19, 0, 360), L([0.42, 0.66], [0.4, 0])] },
  ],
  x: [
    { name: "cross", strokes: [L([0, 0.5], [0.45, 0]), L([0.45, 0.5], [0, 0])] },
    { name: "cross-rev", strokes: [L([0.45, 0.5], [0, 0]), L([0, 0.5], [0.45, 0])] },
    { name: "arcs", strokes: [A(0.02, 0.25, 0.2, 0.25, 80, -80), A(0.43, 0.25, 0.2, 0.25, 100, 260)] },
  ],
  y: [
    { name: "two-lines", strokes: [L([0, 0.5], [0.22, 0.12]), L([0.45, 0.5], [0.08, -0.22])] },
    { name: "cup", strokes: [J(C([0, 0.5], [0.02, 0.05], [0.4, 0.05], [0.42, 0.5]), C([0.42, 0.5], [0.42, 0], [0.4, -0.22], [0.08, -0.2]))] },
  ],
  z: [
    { name: "plain", strokes: [L([0.03, 0.5], [0.45, 0.5], [0.03, 0], [0.47, 0])] },
    { name: "crossed", strokes: [L([0.03, 0.5], [0.45, 0.5], [0.03, 0], [0.47, 0]), L([0.1, 0.25], [0.38, 0.25])] },
  ],
  a: [
    { name: "round-one", strokes: [J(A(0.21, 0.25, 0.2, 0.24, 20, 380), L([0.41, 0.33], [0.41, 0.5], [0.42, 0]))] },
    { name: "round-two", strokes: [A(0.21, 0.25, 0.2, 0.24, 30, 390), L([0.42, 0.5], [0.42, 0])] },
    { name: "print", strokes: [J(A(0.22, 0.36, 0.16, 0.14, 150, 0), L([0.38, 0.36], [0.38, 0.1]), C([0.38, 0.1], [0.38, 0.02], [0.43, 0], [0.47, 0.03])), J(L([0.38, 0.3], [0.2, 0.28]), A(0.2, 0.14, 0.15, 0.14, 90, 290), L([0.25, 0.01], [0.38, 0.1]))] },
  ],
  b: [
    { name: "one", strokes: [J(L([0.06, 0.75], [0.06, 0], [0.06, 0.25]), A(0.25, 0.22, 0.19, 0.22, 170, -190))] },
    { name: "two", strokes: [L([0.06, 0.75], [0.06, 0]), A(0.25, 0.22, 0.19, 0.22, 150, -200)] },
  ],
  c: [
    { name: "arc", strokes: [A(0.25, 0.25, 0.22, 0.25, 50, 310)] },
    { name: "wide", strokes: [A(0.25, 0.25, 0.23, 0.25, 35, 325)] },
  ],
  d: [
    { name: "one", strokes: [J(A(0.21, 0.23, 0.19, 0.23, 20, 380), L([0.4, 0.3], [0.41, 0.75], [0.41, 0]))] },
    { name: "two", strokes: [A(0.21, 0.23, 0.19, 0.23, 30, 390), L([0.42, 0.75], [0.42, 0])] },
  ],
  e: [
    { name: "bar", strokes: [J(L([0.04, 0.26], [0.45, 0.26]), A(0.24, 0.25, 0.21, 0.25, 5, 320))] },
    { name: "loop", strokes: [J(C([0.05, 0.2], [0.35, 0.25], [0.45, 0.45], [0.25, 0.5]), C([0.25, 0.5], [0.0, 0.5], [0.0, 0.0], [0.25, 0.0]), L([0.25, 0], [0.43, 0.08]))] },
  ],
  n: [
    { name: "one", strokes: [J(L([0.05, 0.5], [0.05, 0], [0.05, 0.3]), A(0.23, 0.3, 0.18, 0.2, 170, 0), L([0.41, 0.3], [0.42, 0]))] },
    { name: "two", strokes: [L([0.05, 0.5], [0.05, 0]), J(A(0.23, 0.3, 0.18, 0.2, 170, 0), L([0.41, 0.3], [0.42, 0]))] },
  ],
  t: [
    { name: "hook", strokes: [J(L([0.2, 0.72], [0.2, 0.1]), A(0.3, 0.1, 0.1, 0.1, 180, 330)), L([0.04, 0.5], [0.4, 0.5])] },
    { name: "straight", strokes: [L([0.2, 0.72], [0.2, 0]), L([0.04, 0.5], [0.38, 0.5])] },
  ],
  i: [
    { name: "stem-dot", strokes: [L([0.1, 0.5], [0.1, 0]), dot(0.1, 0.74)] },
    { name: "hook-dot", strokes: [J(L([0.1, 0.5], [0.1, 0.08]), A(0.18, 0.08, 0.08, 0.08, 180, 320)), dot(0.1, 0.74)] },
  ],
  j: [
    { name: "hook-dot", strokes: [J(L([0.2, 0.5], [0.2, -0.1]), A(0.08, -0.1, 0.12, 0.12, 0, -150)), dot(0.2, 0.74)] },
  ],
  l: [
    { name: "stem", strokes: [L([0.1, 0.75], [0.1, 0])] },
    { name: "curl", strokes: [J(L([0.1, 0.75], [0.1, 0.1]), A(0.2, 0.1, 0.1, 0.1, 180, 320))] },
  ],
  "π": [
    { name: "three", strokes: [L([0, 0.48], [0.5, 0.5]), L([0.16, 0.49], [0.13, 0]), J(L([0.36, 0.5], [0.36, 0.08]), A(0.43, 0.08, 0.07, 0.08, 180, 330))] },
    { name: "two", strokes: [J(L([0.13, 0], [0.16, 0.49]), L([0.16, 0.49], [0.5, 0.5])), L([0.37, 0.5], [0.4, 0])] },
    { name: "bar-last", strokes: [L([0.14, 0.5], [0.12, 0]), L([0.37, 0.5], [0.39, 0]), L([0, 0.5], [0.5, 0.5])] },
  ],
  "θ": [
    { name: "two", strokes: [A(0.22, 0.36, 0.19, 0.36, 90, 450), L([0.04, 0.36], [0.4, 0.36])] },
    { name: "one", strokes: [J(A(0.22, 0.36, 0.19, 0.36, 180, 540), L([0.03, 0.36], [0.41, 0.36]))] },
  ],
  "+": [
    { name: "hv", strokes: [L([0.05, 0.29], [0.5, 0.29]), L([0.275, 0.53], [0.275, 0.05])] },
    { name: "vh", strokes: [L([0.275, 0.53], [0.275, 0.05]), L([0.05, 0.29], [0.5, 0.29])] },
  ],
  "-": [
    { name: "short", strokes: [L([0.05, 0.29], [0.45, 0.29])] },
    { name: "long", strokes: [L([0.05, 0.29], [1.2, 0.29])] },
  ],
  "=": [
    { name: "bars", strokes: [L([0.05, 0.4], [0.47, 0.4]), L([0.05, 0.18], [0.47, 0.18])] },
  ],
  "<": [{ name: "angle", strokes: [L([0.45, 0.52], [0.04, 0.27], [0.45, 0.02])] }],
  ">": [{ name: "angle", strokes: [L([0.04, 0.52], [0.45, 0.27], [0.04, 0.02])] }],
  "≤": [
    { name: "two", strokes: [L([0.45, 0.6], [0.04, 0.4], [0.45, 0.2]), L([0.04, 0.02], [0.45, 0.02])] },
    { name: "slanted-bar", strokes: [L([0.45, 0.6], [0.04, 0.4], [0.45, 0.2]), L([0.04, 0.2], [0.45, 0.0])] },
  ],
  "≥": [
    { name: "two", strokes: [L([0.04, 0.6], [0.45, 0.4], [0.04, 0.2]), L([0.04, 0.02], [0.45, 0.02])] },
    { name: "slanted-bar", strokes: [L([0.04, 0.6], [0.45, 0.4], [0.04, 0.2]), L([0.04, 0.0], [0.45, 0.2])] },
  ],
  "÷": [{ name: "bar-dots", strokes: [L([0.05, 0.3], [0.47, 0.3]), dot(0.26, 0.5), dot(0.26, 0.1)] }],
  "/": [{ name: "slash", strokes: [L([0.02, -0.1], [0.4, 0.8])] }],
  "^": [{ name: "caret", strokes: [L([0.02, 0.45], [0.2, 0.75], [0.38, 0.45])] }],
  "(": [
    { name: "arc", strokes: [A(0.45, 0.3, 0.35, 0.5, 115, 245)] },
    { name: "flat", strokes: [A(0.6, 0.3, 0.5, 0.5, 135, 225)] },
  ],
  ")": [
    { name: "arc", strokes: [A(-0.05, 0.3, 0.35, 0.5, 65, -65)] },
    { name: "flat", strokes: [A(-0.2, 0.3, 0.5, 0.5, 45, -45)] },
  ],
  "|": [{ name: "bar", strokes: [L([0.1, 0.8], [0.1, -0.2])] }],
  "!": [{ name: "bar-dot", strokes: [L([0.1, 0.72], [0.1, 0.2]), dot(0.1, 0.04)] }],
  ".": [
    { name: "dot", strokes: [dot(0.08, 0.04)] },
    { name: "tap", strokes: [[[0.08, 0.04]]] },
  ],
  ",": [
    { name: "tick", strokes: [J(A(0.1, 0.04, 0.03, 0.03, 0, 360), C([0.13, 0.04], [0.14, -0.04], [0.1, -0.1], [0.05, -0.13]))] },
    { name: "slash", strokes: [C([0.12, 0.06], [0.13, -0.02], [0.1, -0.08], [0.05, -0.14])] },
  ],
  "√": [
    { name: "short", strokes: [sqrtStroke(0.3)] },
    { name: "mid", strokes: [sqrtStroke(0.8)] },
    { name: "long", strokes: [sqrtStroke(1.6)] },
    { name: "vlong", strokes: [sqrtStroke(3)] },
  ],
  "∫": [
    { name: "s", strokes: [J(A(0.42, 0.85, 0.08, 0.08, 20, 180), C([0.34, 0.85], [0.28, 0.5], [0.22, 0.2], [0.14, -0.15]), A(0.06, -0.15, 0.08, 0.08, 0, -160))] },
    { name: "straight", strokes: [J(A(0.4, 0.85, 0.08, 0.08, 10, 180), L([0.32, 0.85], [0.16, -0.15]), A(0.08, -0.15, 0.08, 0.08, 0, -170))] },
  ],
};

export function bboxOfStrokes(strokes) {
  let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
  for (const s of strokes) for (const p of s) {
    const x = Array.isArray(p) ? p[0] : p.x, y = Array.isArray(p) ? p[1] : p.y;
    if (x < x0) x0 = x; if (x > x1) x1 = x; if (y < y0) y0 = y; if (y > y1) y1 = y;
  }
  return { x0, y0, x1, y1 };
}

// ---------------------------------------------------------------------------------------------
// Tiny typesetter (tests and synthetic data). A spec is:
//   "text"                       a row of single-character glyphs ("*" is not a glyph)
//   [item, item, ...]            a row
//   { sup: spec } / { sub: spec } script attached to the previous row item
//   { frac: [num, den] }         fraction
//   { sqrt: spec }               square root
//   { glyph: "x", variant: 1 }   one glyph with a chosen variant
// Returns boxes in em units, y up, origin at the left end of the baseline:
//   { w, asc, desc, glyphs: [{ char, strokes }] }
function pickVariant(ch, opts, forced) {
  const vs = VARIANTS[ch];
  if (!vs) throw new Error("No glyph for " + JSON.stringify(ch));
  if (forced != null) return vs[forced % vs.length];
  if (opts.variant === "first" || !opts.rng) return vs[0];
  return vs[Math.floor(opts.rng() * vs.length)];
}
function shiftStrokes(strokes, dx, dy, s = 1) {
  return strokes.map((st) => st.map(([x, y]) => [dx + x * s, dy + y * s]));
}
function glyphBox(ch, opts, forced) {
  const v = pickVariant(ch, opts, forced);
  const b = bboxOfStrokes(v.strokes);
  const m = METRICS[ch];
  const left = Math.min(0, b.x0);
  const strokes = shiftStrokes(v.strokes, -left + 0.04, 0);
  return { w: b.x1 - left + 0.12, asc: Math.max(m.hi, b.y1), desc: Math.max(0, -Math.min(m.lo, b.y0)), glyphs: [{ char: ch, strokes }] };
}
function place(box, dx, dy, s = 1) {
  return box.glyphs.map((g) => ({ char: g.char, strokes: shiftStrokes(g.strokes, dx, dy, s) }));
}
function rowBox(items, opts) {
  let x = 0, asc = 0, desc = 0;
  const glyphs = [];
  let prev = null; // { box, x } of the previous base item
  for (const it of items) {
    if (it && typeof it === "object" && it.subsup) {
      // stacked limits (integral bounds)
      const s = 0.62, lo = boxOf(it.subsup[0], opts), hi = boxOf(it.subsup[1], opts);
      const up = prev ? prev.box.asc - hi.asc * s : 0.5, down = prev ? -prev.box.desc + lo.desc * s : -0.2;
      glyphs.push(...place(hi, x + 0.02, up, s), ...place(lo, x - 0.12, down, s));
      x += Math.max(hi.w, lo.w) * s + 0.05;
      asc = Math.max(asc, up + hi.asc * s);
      desc = Math.max(desc, -down + lo.desc * s);
      continue;
    }
    if (it && typeof it === "object" && (it.sup !== undefined || it.sub !== undefined)) {
      const isSup = it.sup !== undefined;
      const inner = boxOf(isSup ? it.sup : it.sub, opts);
      const s = 0.62;
      const dy = isSup ? (prev ? Math.max(0.42, prev.box.asc - 0.28) : 0.42) : -0.2 - (prev ? Math.max(0, prev.box.desc - 0.1) : 0);
      glyphs.push(...place(inner, x + 0.01, dy, s));
      x += inner.w * s + 0.02;
      asc = Math.max(asc, dy + inner.asc * s);
      desc = Math.max(desc, -dy + inner.desc * s);
      continue;
    }
    const b = boxOf(it, opts);
    glyphs.push(...place(b, x, 0));
    prev = { box: b, x };
    x += b.w;
    asc = Math.max(asc, b.asc);
    desc = Math.max(desc, b.desc);
  }
  return { w: x, asc, desc, glyphs };
}
export function boxOf(spec, opts = {}) {
  if (typeof spec === "string") {
    if (spec.length === 1) return glyphBox(spec, opts);
    return rowBox([...spec], opts);
  }
  if (Array.isArray(spec)) return rowBox(spec, opts);
  if (spec.glyph) return glyphBox(spec.glyph, opts, spec.variant);
  if (spec.frac) {
    const num = boxOf(spec.frac[0], opts), den = boxOf(spec.frac[1], opts);
    const w = Math.max(num.w, den.w) + 0.2;
    const axis = 0.29;
    const numY = axis + 0.17 + num.desc, denY = axis - 0.19 - den.asc;
    const glyphs = [
      ...place(num, (w - num.w) / 2, numY),
      { char: "-", strokes: [L([0.05, axis], [w - 0.05, axis])] },
      ...place(den, (w - den.w) / 2, denY),
    ];
    return { w: w + 0.1, asc: numY + num.asc, desc: Math.max(0, -(denY - den.desc)), glyphs };
  }
  if (spec.sqrt !== undefined) {
    const inner = boxOf(spec.sqrt, opts);
    const lo = -inner.desc - 0.05, hi = inner.asc + 0.17;
    const rad = radical(inner.w + 0.12, lo, hi);
    const hook = bboxOfStrokes(rad).x1 - inner.w - 0.12;
    return {
      w: hook + inner.w + 0.2,
      asc: hi + 0.02,
      desc: -lo,
      glyphs: [{ char: "√", strokes: rad }, ...place(inner, hook + 0.06, 0)],
    };
  }
  throw new Error("bad typeset spec");
}

// Lay out a spec and return glyphs in PIXEL coordinates (y down) at the given em size.
export function typeset(spec, { em = 40, x = 20, y = null, rng = null, variant = null } = {}) {
  const box = boxOf(spec, { rng, variant });
  const baseY = y == null ? Math.ceil(box.asc * em) + 20 : y;
  const glyphs = box.glyphs.map((g) => ({
    char: g.char,
    strokes: g.strokes.map((st) => st.map(([gx, gy]) => ({ x: x + gx * em, y: baseY - gy * em }))),
  }));
  return { glyphs, width: Math.ceil(x * 2 + box.w * em), height: Math.ceil(baseY + box.desc * em + 20), baseline: baseY, em };
}
