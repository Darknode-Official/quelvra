// Quelvra vision: public entry point.
//
// Vision only TRANSLATES ink into math text. It never solves, and it never hides uncertainty:
// every symbol carries a confidence and its top alternatives, low-confidence symbols are
// listed, and the produced text is checked with the real parser (result.parseable).
//
//   recognizeStrokes(strokes, opts?)   handwriting from a canvas: [[{x, y, t?}]]
//   recognizeImage(imageData, opts?)   photo / screenshot: {width, height, data (RGBA)}
//   addTemplate(char, strokes)         teach a handwritten symbol (persist with exportTemplates)
//   addImageTemplate(char, imageData, emPx?)  teach a printed glyph
//   exportTemplates() -> JSON string;  importTemplates(json, {replace?})
//   setPhotoTemplates(list)            e.g. buildFontTemplates(browserFontRenderer()) in the UI
//   toEditable(result) -> [{ text, confidence, alternatives, uncertain, structural, symbol }]
//
// Result shape (both recognisers):
//   { text, source: "strokes" | "image", symbols: [{char, confidence, alternatives:[{char, score}],
//     bbox, strokeIds | components}], lowConfidence: [symbol indices], layout, em,
//     confidence (lowest symbol confidence), parseable, parseError: {message, pos, hint} | null }

import { parse } from "../parse.js";
import * as S from "./strokes.js";
import * as P from "./photo.js";
import { renderGlyph } from "./raster.js";

export { buildFontTemplates, browserFontRenderer } from "./photo.js";
export { analyzeLayout } from "./layout.js";

export const LOW_CONFIDENCE = 0.7;
const TEXT = { "π": "pi", "θ": "theta", "÷": "/", "≤": "<=", "≥": ">=", "∫": "int", "√": "sqrt" };

// ---------------------------------------------------------------------------------------------
let basePhoto = null;
const userPhoto = [];
let photoCache = null;

// Built-in photo templates from the pen font in raster.js (several weights, slants, variants).
export function defaultPhotoTemplates() {
  if (basePhoto) return basePhoto;
  const fonts = [];
  for (const weight of [0.07, 0.11]) for (const slant of [0, 0.2]) for (const variant of [0, 1, 2]) {
    fonts.push({ family: `pen-${weight}-${slant}-${variant}`, weight, slant, variant });
  }
  basePhoto = P.buildFontTemplates(renderGlyph, { fonts });
  return basePhoto;
}
export function setPhotoTemplates(list, { keepBuiltin = true } = {}) {
  if (!Array.isArray(list)) throw new Error("setPhotoTemplates expects an array of templates");
  basePhoto = keepBuiltin ? [...(basePhoto || defaultPhotoTemplates()), ...list] : list;
  photoCache = null;
}
function photoTemplates() {
  if (!photoCache) photoCache = [...defaultPhotoTemplates(), ...userPhoto];
  return photoCache;
}

// ---------------------------------------------------------------------------------------------
function finalize(r, source) {
  let parseable = false, parseError = null;
  if (!r.text) parseError = { message: "Nothing was recognised", pos: 0, hint: "Write or photograph an expression" };
  else {
    try { parse(r.text); parseable = true; } catch (e) {
      parseError = { message: e.message, pos: typeof e.pos === "number" ? e.pos : null, hint: e.hint || "" };
    }
  }
  const confidence = r.symbols.length ? Math.min(...r.symbols.map((s) => s.confidence)) : 0;
  return { ...r, source, confidence, parseable, parseError };
}

export function recognizeStrokes(strokes, opts = {}) {
  return finalize(S.recognizeStrokes(strokes, { threshold: LOW_CONFIDENCE, ...opts }), "strokes");
}

export function recognizeImage(imageData, opts = {}) {
  const templates = opts.templates || photoTemplates();
  return finalize(P.recognizeImage(imageData, { threshold: LOW_CONFIDENCE, ...opts, templates }), "image");
}

export function addTemplate(char, strokes) { return S.addTemplate(char, strokes); }
export function addImageTemplate(char, imageData, emPx = null) {
  userPhoto.push(P.templateFromImage(char, imageData, emPx));
  photoCache = null;
  return userPhoto.length;
}
export function clearTemplates() { S.clearUserTemplates(); userPhoto.length = 0; photoCache = null; }

export function exportTemplates() {
  const strokes = JSON.parse(S.exportUserTemplates()).templates;
  const images = userPhoto.map((t) => ({ char: t.char, size: t.size, feat: Array.from(t.feat, (v) => Math.round(v * 1e4) / 1e4) }));
  return JSON.stringify({ format: "quelvra-vision-templates", version: 1, strokes, images });
}
export function importTemplates(json, { replace = false } = {}) {
  const o = typeof json === "string" ? JSON.parse(json) : json;
  if (!o || o.format !== "quelvra-vision-templates") throw new Error("Not a Quelvra vision template file");
  if (replace) clearTemplates();
  S.importUserTemplates({ format: "quelvra-stroke-templates", version: 1, templates: o.strokes || [] });
  for (const t of o.images || []) {
    if (!t || typeof t.char !== "string" || !Array.isArray(t.feat)) continue;
    userPhoto.push({ char: t.char, size: t.size ?? null, feat: Float32Array.from(t.feat), font: "user", user: true });
  }
  photoCache = null;
  return { strokes: S.userTemplateCount(), images: userPhoto.length };
}

// ---------------------------------------------------------------------------------------------
// Editable tokens for the UI: the recognised text split into runs that come from one symbol
// (with its confidence and alternatives) and structural runs the layout inserted ("(", ")/(",
// "^(", spaces), which carry no uncertainty of their own.
export function toEditable(result, { threshold = LOW_CONFIDENCE } = {}) {
  const text = result.text || "";
  const charMap = (result.layout && result.layout.charMap) || new Array(text.length).fill(-1);
  const tokens = [];
  let i = 0;
  while (i < text.length) {
    const sym = charMap[i];
    let j = i + 1;
    while (j < text.length && charMap[j] === sym && (sym >= 0 || text[j] !== " ")) j++;
    const piece = text.slice(i, j);
    if (sym >= 0) {
      const s = result.symbols[sym];
      tokens.push({
        text: piece, symbol: sym, confidence: s.confidence,
        alternatives: (s.alternatives || []).map((a) => ({ text: TEXT[a.char] ?? a.char, char: a.char, score: a.score })),
        uncertain: s.confidence < threshold, structural: false, start: i, end: j,
        ...(s.context ? { note: s.context } : {}),
      });
    } else {
      tokens.push({ text: piece, symbol: -1, confidence: 1, alternatives: [], uncertain: false, structural: true, start: i, end: j });
    }
    i = j;
  }
  if (result.parseError && typeof result.parseError.pos === "number") {
    const t = tokens.find((k) => result.parseError.pos >= k.start && result.parseError.pos < k.end) || tokens[tokens.length - 1];
    if (t) t.parseError = true;
  }
  return tokens;
}
