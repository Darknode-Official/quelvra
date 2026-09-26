// Quelvra vision: a tiny vector rasterizer with no canvas.
//
// Draws pen-stroke glyphs (from glyphs.js) into RGBA bitmaps shaped like ImageData
// ({ width, height, data: Uint8ClampedArray }). Used in Node tests to build photo templates and
// to synthesize test "photos" (rotation, blur-free anti-aliasing, noise), and usable in the
// browser as a fallback template source when OffscreenCanvas fonts are unavailable.

import { VARIANTS, METRICS, bboxOfStrokes, typeset } from "./glyphs.js";

export function createImage(width, height, gray = 255) {
  width = Math.max(1, Math.round(width));
  height = Math.max(1, Math.round(height));
  const data = new Uint8ClampedArray(width * height * 4);
  for (let i = 0; i < data.length; i += 4) { data[i] = data[i + 1] = data[i + 2] = gray; data[i + 3] = 255; }
  return { width, height, data };
}

// Coverage buffer (0..1 ink) -> RGBA (black ink on white paper by default).
function inkInto(img, cov, ink = 0, paper = null) {
  const { data } = img;
  for (let i = 0; i < cov.length; i++) {
    const c = cov[i];
    if (c <= 0) continue;
    const j = i * 4;
    for (let k = 0; k < 3; k++) data[j + k] = Math.round(data[j + k] * (1 - c) + ink * c);
  }
  return img;
}

function drawSegment(cov, W, H, ax, ay, bx, by, r) {
  const x0 = Math.max(0, Math.floor(Math.min(ax, bx) - r - 1)), x1 = Math.min(W - 1, Math.ceil(Math.max(ax, bx) + r + 1));
  const y0 = Math.max(0, Math.floor(Math.min(ay, by) - r - 1)), y1 = Math.min(H - 1, Math.ceil(Math.max(ay, by) + r + 1));
  const dx = bx - ax, dy = by - ay, L2 = dx * dx + dy * dy;
  for (let y = y0; y <= y1; y++) {
    for (let x = x0; x <= x1; x++) {
      const px = x + 0.5, py = y + 0.5;
      let t = L2 > 0 ? ((px - ax) * dx + (py - ay) * dy) / L2 : 0;
      t = t < 0 ? 0 : t > 1 ? 1 : t;
      const d = Math.hypot(px - (ax + t * dx), py - (ay + t * dy));
      const c = r + 0.5 - d;
      if (c > 0) { const k = y * W + x; const v = c > 1 ? 1 : c; if (v > cov[k]) cov[k] = v; }
    }
  }
}

// strokes: [[{x,y}]] in pixel coordinates; width: pen width in pixels.
export function drawStrokes(img, strokes, width = 3, ink = 0) {
  const W = img.width, H = img.height;
  const cov = new Float32Array(W * H);
  const r = Math.max(0.5, width / 2);
  for (const s of strokes) {
    if (s.length === 1) drawSegment(cov, W, H, s[0].x, s[0].y, s[0].x, s[0].y, r * 1.3);
    for (let i = 1; i < s.length; i++) drawSegment(cov, W, H, s[i - 1].x, s[i - 1].y, s[i].x, s[i].y, r);
  }
  return inkInto(img, cov, ink);
}

// Font "families" for the built-in pen font: pen weight (em), slant, and default variant.
export const PEN_FONTS = [
  { family: "sans", weight: 0.07, slant: 0, variant: 0 },
  { family: "bold", weight: 0.11, slant: 0, variant: 0 },
  { family: "italic", weight: 0.08, slant: 0.2, variant: 0 },
  { family: "alt", weight: 0.08, slant: 0.05, variant: 1 },
];

function slantStrokes(strokes, slant, baseY) {
  if (!slant) return strokes;
  return strokes.map((s) => s.map((p) => ({ x: p.x + slant * (baseY - p.y), y: p.y })));
}

// renderGlyph(char, fontSpec) -> ImageData-like with the glyph drawn at the requested size.
// fontSpec: { size (px per em, default 48), weight (em), slant, variant }.
export function renderGlyph(ch, fontSpec = {}) {
  const vs = VARIANTS[ch];
  if (!vs) return null;
  const size = fontSpec.size || 48;
  const v = vs[(fontSpec.variant || 0) % vs.length];
  const m = METRICS[ch];
  const b = bboxOfStrokes(v.strokes);
  const pad = 0.3;
  const top = Math.max(m.hi, b.y1) + pad, bottom = Math.min(m.lo, b.y0) - pad;
  const W = Math.ceil((b.x1 - Math.min(0, b.x0) + 2 * pad + 0.3) * size), H = Math.ceil((top - bottom) * size);
  const img = createImage(W, H);
  const ox = (pad - Math.min(0, b.x0)) * size, baseY = top * size;
  let strokes = v.strokes.map((s) => s.map(([x, y]) => ({ x: ox + x * size, y: baseY - y * size })));
  strokes = slantStrokes(strokes, fontSpec.slant || 0, baseY);
  return drawStrokes(img, strokes, Math.max(1, (fontSpec.weight || 0.07) * size));
}

// Render a typeset spec (see glyphs.typeset) to a bitmap.
export function renderMath(spec, { em = 40, weight = 0.08, slant = 0, rng = null, variant = null, margin = 20 } = {}) {
  const t = typeset(spec, { em, x: margin, rng, variant });
  const img = createImage(t.width, t.height);
  const all = [];
  for (const g of t.glyphs) all.push(...slantStrokes(g.strokes, slant, t.baseline));
  drawStrokes(img, all, Math.max(1, weight * em));
  return img;
}

// Rotate an image about its centre by `deg` degrees (bilinear, paper-coloured fill).
export function rotateImage(img, deg, fill = 255) {
  const { width: W, height: H, data } = img;
  const a = (deg * Math.PI) / 180, c = Math.cos(a), s = Math.sin(a);
  const W2 = Math.ceil(Math.abs(W * c) + Math.abs(H * s)), H2 = Math.ceil(Math.abs(W * s) + Math.abs(H * c));
  const out = createImage(W2, H2, fill);
  const cx = W / 2, cy = H / 2, cx2 = W2 / 2, cy2 = H2 / 2;
  for (let y = 0; y < H2; y++) {
    for (let x = 0; x < W2; x++) {
      const dx = x + 0.5 - cx2, dy = y + 0.5 - cy2;
      const sx = c * dx + s * dy + cx - 0.5, sy = -s * dx + c * dy + cy - 0.5;
      const x0 = Math.floor(sx), y0 = Math.floor(sy), fx = sx - x0, fy = sy - y0;
      let v = 0;
      for (const [xx, yy, w] of [[x0, y0, (1 - fx) * (1 - fy)], [x0 + 1, y0, fx * (1 - fy)], [x0, y0 + 1, (1 - fx) * fy], [x0 + 1, y0 + 1, fx * fy]]) {
        const g = xx >= 0 && yy >= 0 && xx < W && yy < H ? data[(yy * W + xx) * 4] : fill;
        v += w * g;
      }
      const j = (y * W2 + x) * 4;
      out.data[j] = out.data[j + 1] = out.data[j + 2] = Math.round(v);
    }
  }
  return out;
}

// Additive Gaussian-ish noise, optional salt-and-pepper specks and an illumination gradient.
export function addNoise(img, rand, { sigma = 20, specks = 0, gradient = 0 } = {}) {
  const { width: W, height: H, data } = img;
  const gauss = () => { let s = 0; for (let k = 0; k < 6; k++) s += rand(); return (s - 3) * 1.41; };
  for (let y = 0; y < H; y++) for (let x = 0; x < W; x++) {
    const j = (y * W + x) * 4;
    const shade = gradient ? -gradient * (x / W) : 0;
    const v = data[j] + gauss() * sigma + shade;
    data[j] = data[j + 1] = data[j + 2] = Math.max(0, Math.min(255, Math.round(v)));
  }
  for (let k = 0; k < specks; k++) {
    const x = Math.floor(rand() * W), y = Math.floor(rand() * H), j = (y * W + x) * 4;
    const v = rand() < 0.5 ? 0 : 255;
    data[j] = data[j + 1] = data[j + 2] = v;
  }
  return img;
}

// Debug helper: ASCII art of a bitmap (dark pixels as #).
export function toAscii(img, step = 2, thr = 128) {
  let s = "";
  for (let y = 0; y < img.height; y += step) {
    let row = "";
    for (let x = 0; x < img.width; x += Math.max(1, step >> 1)) row += img.data[(y * img.width + x) * 4] < thr ? "#" : ".";
    s += row + "\n";
  }
  return s;
}
