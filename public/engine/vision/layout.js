// Quelvra vision: 2D structure analysis shared by the stroke and photo recognisers.
//
//   analyzeLayout(symbols, opts) -> { text, map, charMap, lines, tree, em }
//
// symbols: [{ char, bbox: {x0, y0, x1, y1} (pixels, y DOWN), confidence?, ... }]
// Steps: estimate the text size (em) from symbol metrics, split into lines by vertical gaps,
// find fraction bars (a "-" with symbols above AND below inside its span) and radicals (a "√"
// and the symbols it contains), then read each row left to right, deciding superscript /
// subscript / same-baseline from each symbol's estimated baseline, math axis and relative size.
// The result is parser-ready text such as "(x+1)/(2)" or "x^(2)+1", plus a map from text
// positions back to symbol indices so the UI can highlight uncertain characters.
//
// Layout never guesses silently: structures it cannot express in parser syntax (for example a
// compound subscript) are still emitted and the caller's parse check flags them.

import { METRICS } from "./glyphs.js";

const AXIS = 0.29; // math axis height (em) used by the glyph metrics
const TEXT = { "π": "pi", "θ": "theta", "÷": "/", "≤": "<=", "≥": ">=", "∫": "int", "√": "sqrt" };
const NO_SCRIPT = new Set(["+", "-", "=", "<", ">", "≤", "≥", "÷", "/", ",", ".", "^", "(", "!"]);

function median(a) {
  if (!a.length) return NaN;
  const s = [...a].sort((p, q) => p - q);
  const m = s.length >> 1;
  return s.length % 2 ? s[m] : (s[m - 1] + s[m]) / 2;
}

// Size of one em implied by a symbol's height (null when the symbol does not tell the size).
export function symbolEm(char, bbox) {
  const m = METRICS[char];
  if (!m || m.kind === "flat" || m.kind === "dot" || char === "√" || char === "+" || char === "÷") return null;
  const h = bbox.y1 - bbox.y0;
  if (!(h > 0)) return null;
  return h / (m.hi - m.lo);
}

// Robust text size for a set of symbols: median of per-symbol estimates, weighted toward
// confident symbols. Falls back to typical-size guesses and finally to opts.em.
export function estimateEm(symbols, fallback = null) {
  const ests = [];
  for (const s of symbols) {
    const e = symbolEm(s.char, s.bbox);
    if (e) { ests.push(e); if ((s.confidence ?? 1) > 0.8) ests.push(e); }
  }
  if (ests.length) return median(ests);
  const dims = symbols.map((s) => Math.max(s.bbox.x1 - s.bbox.x0, s.bbox.y1 - s.bbox.y0)).filter((d) => d > 0);
  if (fallback) return fallback;
  return dims.length ? median(dims) / 0.6 : 40;
}

function unionBox(nodes) {
  let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
  for (const n of nodes) {
    const b = n.bbox;
    if (b.x0 < x0) x0 = b.x0; if (b.y0 < y0) y0 = b.y0; if (b.x1 > x1) x1 = b.x1; if (b.y1 > y1) y1 = b.y1;
  }
  return { x0, y0, x1, y1 };
}
const cx = (b) => (b.x0 + b.x1) / 2;
const cy = (b) => (b.y0 + b.y1) / 2;

// Geometry of a leaf symbol: em (or null), baseline and axis y (pixels, y down).
function leaf(sym, idx, emGlobal) {
  const b = sym.bbox;
  const m = METRICS[sym.char];
  const em = symbolEm(sym.char, b);
  let baseline = null, axis;
  if (em) {
    baseline = b.y1 + m.lo * em;
    axis = baseline - AXIS * em;
  } else if (sym.char === ".") {
    baseline = b.y1;
    axis = baseline - AXIS * emGlobal;
  } else if (sym.char === ",") {
    baseline = b.y0 + 0.07 * emGlobal;
    axis = baseline - AXIS * emGlobal;
  } else if (sym.char === "^") {
    axis = b.y1 + (0.45 - AXIS) * emGlobal;
  } else {
    axis = cy(b);
  }
  if (sym.char === "∫") axis = cy(b) + (0.35 - AXIS) * (em || emGlobal);
  return { type: "sym", idx, char: sym.char, bbox: b, em, baseline, axis };
}

// ---------------------------------------------------------------------------------------------
// Context re-ranking that only needs geometry: a vertical stroke read as "1" or "l" that reaches
// clearly below the line's baseline is an absolute-value bar. The symbol's confidence is NOT
// raised (the shape alone was ambiguous); the symbol records why its reading changed.
const BAR_FAMILY = new Set(["1", "l", "|"]);
export function contextRerank(symbols, opts = {}) {
  const em = opts.em || estimateEm(symbols);
  const baselines = [];
  symbols.forEach((s, i) => {
    const m = METRICS[s.char];
    if (!m || BAR_FAMILY.has(s.char) || (s.confidence ?? 1) < 0.6) return;
    if (m.kind === "digit" || (m.kind === "letter" && m.lo === 0)) baselines.push({ i, y: s.bbox.y1, y0: s.bbox.y0 });
  });
  const cands = [];
  for (const s of symbols) {
    if (!BAR_FAMILY.has(s.char)) continue;
    const near = baselines.filter((b) => b.y > s.bbox.y0 && b.y0 < s.bbox.y1);
    if (!near.length) continue;
    const base = median(near.map((b) => b.y));
    const top = Math.min(...near.map((b) => b.y0));
    if (s.bbox.y1 - base > 0.06 * em && s.bbox.y0 <= top + 0.15 * em && s.bbox.y1 - s.bbox.y0 > 0.7 * em) cands.push(s);
  }
  // bars come in pairs: convert only when at least two tall descending strokes share a line
  for (const s of cands) {
    const partner = cands.some((o) => o !== s && Math.abs(o.bbox.y1 - s.bbox.y1) < 0.25 * em && Math.abs(o.bbox.y0 - s.bbox.y0) < 0.3 * em);
    if (!partner || s.char === "|") continue;
    const alt = (s.alternatives || []).find((a) => a.char === "|");
    s.alternatives = [{ char: s.char, score: s.confidence }, ...(s.alternatives || []).filter((a) => a.char !== "|")].slice(0, 3);
    s.char = "|";
    s.confidence = Math.min(s.confidence, alt ? alt.score : 0.5, 0.6);
    s.context = "tall stroke reaching below the baseline, paired with another: read as an absolute-value bar";
  }
  return symbols;
}

// ---------------------------------------------------------------------------------------------
// Region parsing: pull out fractions and radicals (widest first), then read the row.
function claimAboveBelow(bar, nodes, em) {
  const b = bar.bbox, w = b.x1 - b.x0, tol = 0.08 * w;
  const inSpan = (n) => cx(n.bbox) >= b.x0 - tol && cx(n.bbox) <= b.x1 + tol;
  const barY = cy(b);
  const gather = (up) => {
    const cand = nodes.filter((n) => n !== bar && inSpan(n) && (up ? cy(n.bbox) < barY : cy(n.bbox) > barY));
    cand.sort((p, q) => (up ? q.bbox.y1 - p.bbox.y1 : p.bbox.y0 - q.bbox.y0));
    const out = [];
    let edge = up ? b.y0 : b.y1;
    for (const n of cand) {
      const gap = up ? edge - n.bbox.y1 : n.bbox.y0 - edge;
      if (gap > 0.7 * em) break;
      out.push(n);
      edge = up ? Math.min(edge, n.bbox.y0) : Math.max(edge, n.bbox.y1);
    }
    return out;
  };
  return { above: gather(true), below: gather(false) };
}

function sqrtMembers(rad, nodes, em) {
  const b = rad.bbox, h = b.y1 - b.y0, w = b.x1 - b.x0;
  const left = b.x0 + 0.3 * Math.min(w, h);
  // members start under the overbar (short handwritten overbars are common, so a symbol that
  // starts just before the bar ends still counts) and sit vertically inside the sign
  return nodes.filter((n) => n !== rad && cx(n.bbox) > left && (cx(n.bbox) < b.x1 || n.bbox.x0 < b.x1 - 0.02 * em) && cy(n.bbox) > b.y0 && cy(n.bbox) < b.y1 + 0.1 * em);
}

function parseRegion(nodes, em) {
  nodes = [...nodes];
  const rejected = new Set();
  for (let guard = 0; guard < 200; guard++) {
    const cands = nodes.filter((n) => n.type === "sym" && (n.char === "-" || n.char === "√") && !rejected.has(n));
    if (!cands.length) break;
    cands.sort((p, q) => (q.bbox.x1 - q.bbox.x0) - (p.bbox.x1 - p.bbox.x0));
    const c = cands[0];
    if (c.char === "-") {
      const { above, below } = claimAboveBelow(c, nodes, em);
      if (!above.length || !below.length) { rejected.add(c); continue; }
      const members = new Set([...above, ...below]);
      const num = parseRegion(above, em), den = parseRegion(below, em);
      const node = {
        type: "frac", bar: c.idx, num, den,
        bbox: unionBox([c, ...above, ...below]),
        axis: cy(c.bbox), em: median([num.em, den.em].filter(Boolean)) || em, baseline: null,
      };
      nodes = nodes.filter((n) => n !== c && !members.has(n));
      nodes.push(node);
    } else {
      const inner = sqrtMembers(c, nodes, em);
      const members = new Set(inner);
      const body = parseRegion(inner, em);
      const node = {
        type: "sqrt", rad: c.idx, body,
        bbox: unionBox([c, ...inner]),
        axis: inner.length ? body.axis : cy(c.bbox), em: body.em || em, baseline: inner.length ? body.baseline : null,
      };
      nodes = nodes.filter((n) => n !== c && !members.has(n));
      nodes.push(node);
    }
  }
  return buildRow(nodes, em);
}

function canTakeScript(n) {
  if (n.type === "frac") return false;
  if (n.type === "sqrt") return true;
  return !NO_SCRIPT.has(n.char);
}

// Where does `it` sit relative to `base`?  "sup" | "sub" | "same"
const NO_SCRIPT_START = new Set(["+", "=", "<", ">", "≤", "≥", "÷", ",", ".", "!", ")"]);
function relation(base, it, em, inScript = false) {
  if (!canTakeScript(base)) return "same";
  if (!inScript && it.type === "sym" && NO_SCRIPT_START.has(it.char)) return "same";
  // the base's own size estimate is noisy for single symbols: temper it with the line's em
  const bem = base.em ? Math.sqrt(base.em * em) : em;
  if (it.bbox.x0 < base.bbox.x0 + 0.25 * (base.bbox.x1 - base.bbox.x0)) return "same";
  const big = base.type === "sym" && base.char === "∫";
  if (big) {
    // integral bounds: above the middle -> upper limit; below -> lower limit
    const mid = cy(base.bbox), h = base.bbox.y1 - base.bbox.y0;
    const itc = cy(it.bbox);
    const small = it.em ? it.em < 0.85 * (base.em || em) * 1.0 : (it.bbox.y1 - it.bbox.y0) < 0.45 * h;
    if (!small) return "same";
    if (it.bbox.x0 > base.bbox.x1 + 0.6 * em) return "same";
    if (itc < mid - 0.22 * h) return "sup";
    if (itc > mid + 0.22 * h) return "sub";
    return "same";
  }
  const ratio = it.em ? it.em / bem : null;
  if (base.baseline != null && it.baseline != null) {
    const d = (base.baseline - it.baseline) / bem; // positive: it is raised
    const smaller = ratio != null && ratio < 0.85;
    const bc = cy(base.bbox);
    if (d > 0.5 || (d > 0.3 && it.bbox.y1 < bc) || (smaller && (d > 0.2 || it.bbox.y1 < bc))) return "sup";
    if (d < -0.4 || (d < -0.3 && it.bbox.y0 > bc) || (smaller && (d < -0.08 || it.bbox.y0 > bc - 0.05 * bem))) return "sub";
    return "same";
  }
  const d = (base.axis - it.axis) / bem;
  if (d > 0.27) return "sup";
  if (d < -0.27) return "sub";
  return "same";
}

function buildRow(nodes, em) {
  nodes = [...nodes].sort((p, q) => p.bbox.x0 - q.bbox.x0 || p.bbox.y0 - q.bbox.y0);
  const elems = [];
  let i = 0;
  while (i < nodes.length) {
    const n = nodes[i];
    const last = elems[elems.length - 1];
    const rel = last ? relation(last.node, n, em) : "same";
    if (rel === "same") { elems.push({ node: n, sup: null, sub: null }); i++; continue; }
    let j = i;
    while (j < nodes.length && relation(last.node, nodes[j], em, true) === rel) j++;
    const group = nodes.slice(i, j);
    const row = buildRow(group, em);
    if (last[rel]) last[rel] = { type: "row", elems: [...last[rel].elems, ...row.elems], bbox: unionBox([last[rel], row]) };
    else last[rel] = row;
    i = j;
  }
  const bbox = nodes.length ? unionBox(nodes) : { x0: 0, y0: 0, x1: 0, y1: 0 };
  const bases = elems.map((e) => e.node);
  const ems = bases.map((b) => b.em).filter(Boolean);
  const axes = bases.filter((b) => b.type !== "sym" || b.em).map((b) => b.axis);
  const baselines = bases.map((b) => b.baseline).filter((v) => v != null);
  return {
    type: "row", elems, bbox,
    em: ems.length ? median(ems) : null,
    axis: axes.length ? median(axes) : (bases.length ? median(bases.map((b) => b.axis)) : 0),
    baseline: baselines.length ? median(baselines) : null,
  };
}

// ---------------------------------------------------------------------------------------------
// Text emission with a position map.
class Emitter {
  constructor() { this.text = ""; this.map = []; }
  put(s, idx = -1, glue = true) {
    if (glue && this.text && s) {
      const a = this.text[this.text.length - 1], b = s[0];
      // letters must not fuse into words (t a n -> tan) or into letter-digit subscripts (x2 -> x_2)
      if (/[A-Za-z]/.test(a) && /[A-Za-z0-9]/.test(b)) this.text += " ";
    }
    const start = this.text.length;
    this.text += s;
    if (idx >= 0) this.map.push({ start, end: this.text.length, symbol: idx });
  }
}

function emitNode(n, E, symbols, alone) {
  if (n.type === "sym") { E.put(TEXT[n.char] ?? n.char, n.idx); return; }
  if (n.type === "row") { emitRow(n, E, symbols); return; }
  if (n.type === "frac") {
    if (!alone) E.put("(");
    E.put("(");
    emitRow(n.num, E, symbols);
    E.put(")", -1, false);
    E.put("/", n.bar, false);
    E.put("(", -1, false);
    emitRow(n.den, E, symbols);
    E.put(")", -1, false);
    if (!alone) E.put(")", -1, false);
    return;
  }
  if (n.type === "sqrt") {
    E.put("sqrt", n.rad);
    E.put("(", -1, false);
    emitRow(n.body, E, symbols);
    E.put(")", -1, false);
  }
}

function simpleText(row, symbols) {
  const E = new Emitter();
  emitRow(row, E, symbols);
  return E;
}

function emitRow(row, E, symbols) {
  const alone = row.elems.length === 1 && !row.elems[0].sup && !row.elems[0].sub;
  row.elems.forEach((e) => {
    const base = e.node;
    emitNode(base, E, symbols, alone);
    const isInt = base.type === "sym" && base.char === "∫";
    if (e.sub) {
      const inner = simpleText(e.sub, symbols);
      if (!isInt && /^[A-Za-z0-9]+$/.test(inner.text)) {
        E.put("_", -1, false);
        const off = E.text.length;
        E.text += inner.text;
        for (const m of inner.map) E.map.push({ start: m.start + off, end: m.end + off, symbol: m.symbol });
      } else {
        E.put("_(", -1, false);
        const off = E.text.length;
        E.text += inner.text;
        for (const m of inner.map) E.map.push({ start: m.start + off, end: m.end + off, symbol: m.symbol });
        E.put(")", -1, false);
      }
    }
    if (e.sup) {
      E.put("^(", -1, false);
      const inner = simpleText(e.sup, symbols);
      const off = E.text.length;
      E.text += inner.text;
      for (const m of inner.map) E.map.push({ start: m.start + off, end: m.end + off, symbol: m.symbol });
      E.put(")", -1, false);
    }
  });
}

// Split into lines where no symbol covers a vertical band of at least `gap` pixels.
function splitLines(nodes, gap) {
  const sorted = [...nodes].sort((p, q) => p.bbox.y0 - q.bbox.y0);
  const lines = [];
  let cur = [], bottom = -Infinity;
  for (const n of sorted) {
    if (cur.length && n.bbox.y0 - bottom > gap) { lines.push(cur); cur = []; bottom = -Infinity; }
    cur.push(n);
    bottom = Math.max(bottom, n.bbox.y1);
  }
  if (cur.length) lines.push(cur);
  return lines;
}

function strip(n) {
  if (n.type === "sym") return { type: "sym", symbol: n.idx, char: n.char };
  if (n.type === "row") return { type: "row", items: n.elems.map((e) => ({ base: strip(e.node), sup: e.sup && strip(e.sup), sub: e.sub && strip(e.sub) })) };
  if (n.type === "frac") return { type: "frac", bar: n.bar, num: strip(n.num), den: strip(n.den) };
  return { type: "sqrt", radical: n.rad, body: strip(n.body) };
}

export function analyzeLayout(symbols, opts = {}) {
  if (!symbols.length) return { text: "", map: [], charMap: [], lines: [], tree: [], em: opts.em || null };
  const em = opts.em || estimateEm(symbols);
  const leaves = symbols.map((s, i) => leaf(s, i, em));
  const lines = splitLines(leaves, 0.55 * em);
  const E = new Emitter();
  const tree = [];
  const lineInfo = [];
  lines.forEach((ln, k) => {
    if (k) E.put("; ", -1, false);
    const start = E.text.length;
    const row = parseRegion(ln, em);
    emitRow(row, E, symbols);
    tree.push(strip(row));
    lineInfo.push({ start, end: E.text.length, symbols: ln.map((n) => n.idx), bbox: unionBox(ln) });
  });
  const charMap = new Array(E.text.length).fill(-1);
  for (const m of E.map) for (let p = m.start; p < m.end; p++) charMap[p] = m.symbol;
  return { text: E.text, map: E.map, charMap, lines: lineInfo, tree, em };
}
