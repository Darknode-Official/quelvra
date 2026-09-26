import { test, eq, ok, rng } from "./harness.js";
import { parse } from "../public/engine/parse.js";
import { VARIANTS, typeset, bboxOfStrokes } from "../public/engine/vision/glyphs.js";
import { distortStrokes, synthesizeStrokes } from "../public/engine/vision/strokes.js";
import { renderMath, rotateImage, addNoise } from "../public/engine/vision/raster.js";
import { analyzeLayout } from "../public/engine/vision/layout.js";
import {
  recognizeStrokes, recognizeImage, addTemplate, exportTemplates, importTemplates, clearTemplates, toEditable, LOW_CONFIDENCE,
} from "../public/engine/vision/index.js";

const NEAT = { rot: 4, shear: 0.08, jitter: 0.008, wobble: 0.015 };
const parses = (s) => { try { parse(s); return true; } catch (_) { return false; } };
// The contract: text either parses, or the result says it does not (never silently wrong syntax).
function checkContract(r) {
  ok(typeof r.text === "string", "text is a string");
  eq(r.parseable, parses(r.text), `parseable flag for ${JSON.stringify(r.text)}`);
  if (!r.parseable) ok(r.parseError && typeof r.parseError.message === "string", "parseError explains the failure");
  for (const s of r.symbols) {
    ok(s.confidence >= 0 && s.confidence <= 1, "confidence in [0,1]");
    ok(Array.isArray(s.alternatives), "alternatives listed");
  }
  const low = r.symbols.map((s, i) => (s.confidence < LOW_CONFIDENCE ? i : -1)).filter((i) => i >= 0);
  eq(JSON.stringify(r.lowConfidence), JSON.stringify(low), "lowConfidence lists exactly the uncertain symbols");
}

// ---------------------------------------------------------------------------------------------
// 1. single symbols from synthesized strokes (held-out jitter: different seed from templates)
test("strokes: single-symbol accuracy on jittered, scaled, rotated samples", () => {
  const R = rng(2024);
  let n = 0, top1 = 0, top3 = 0;
  const miss = {};
  for (const [ch, vs] of Object.entries(VARIANTS)) for (const v of vs) for (let k = 0; k < 4; k++) {
    const em = 28 + R.next() * 44;
    const strokes = distortStrokes(v.strokes, R.next, { em, x: 80 + R.next() * 200, y: 150 + R.next() * 100 });
    const r = recognizeStrokes(strokes, { em });
    n++;
    const s = r.symbols.length === 1 ? r.symbols[0] : null;
    const cands = s ? [s.char, ...s.alternatives.map((a) => a.char)] : [];
    if (cands[0] === ch) top1++; else miss[ch] = (miss[ch] || 0) + 1;
    if (cands.slice(0, 3).includes(ch)) top3++;
  }
  const a1 = top1 / n, a3 = top3 / n;
  console.log(`     vision strokes: n=${n} top-1 ${(100 * a1).toFixed(1)}% top-3 ${(100 * a3).toFixed(1)}%  misses ${JSON.stringify(miss)}`);
  ok(a1 >= 0.9, `top-1 ${a1}`);
  ok(a3 >= 0.98, `top-3 ${a3}`);
});

test("strokes: clean templates are recognised with high confidence", () => {
  for (const ch of ["2", "x", "+", "=", "7", "π", "θ", "√", "∫", "(", "≤"]) {
    const strokes = VARIANTS[ch][0].strokes.map((s) => s.map(([x, y]) => ({ x: 100 + x * 50, y: 200 - y * 50 })));
    const r = recognizeStrokes(strokes, { em: 50 });
    eq(r.symbols.length, 1, ch);
    eq(r.symbols[0].char, ch, ch);
    ok(r.symbols[0].confidence >= LOW_CONFIDENCE, `${ch} confidence ${r.symbols[0].confidence}`);
  }
});

// ---------------------------------------------------------------------------------------------
// 2. multi-symbol handwriting
const EXPR = [
  [["x", { sup: "2" }, "+1"], "x^(2)+1"],
  ["2x=6", "2x=6"],
  [{ frac: ["a+b", "c"] }, "(a+b)/(c)"],
  [[{ sqrt: "x+1" }], "sqrt(x+1)"],
  [["x", { sub: "1" }], "x_1"],
  [["y=4x", { sup: "3" }, "-9"], "y=4x^(3)-9"],
];
for (const [spec, want] of EXPR) {
  test(`strokes: neat handwriting of ${want}`, () => {
    const R = rng(want.length * 131 + 7);
    let exact = 0;
    const N = 6;
    for (let k = 0; k < N; k++) {
      const { strokes } = synthesizeStrokes(spec, R.next, { em: 32 + R.next() * 28, ...NEAT });
      const r = recognizeStrokes(strokes);
      checkContract(r);
      if (r.text === want) exact++;
    }
    ok(exact >= N - 1, `${exact}/${N} exact`);
  });
}

test("strokes: fraction and radical structure is reported in the layout tree", () => {
  const R = rng(5);
  const { strokes } = synthesizeStrokes({ frac: ["a+b", "c"] }, R.next, { em: 40, rot: 0, shear: 0, aniso: 0, jitter: 0, wobble: 0, drift: 0 });
  const r = recognizeStrokes(strokes);
  eq(r.text, "(a+b)/(c)");
  eq(r.layout.tree[0].items[0].base.type, "frac");
  const { strokes: s2 } = synthesizeStrokes([{ sqrt: "x+1" }], R.next, { em: 40, rot: 0, shear: 0, aniso: 0, jitter: 0, wobble: 0, drift: 0 });
  const r2 = recognizeStrokes(s2);
  eq(r2.text, "sqrt(x+1)");
  eq(r2.layout.tree[0].items[0].base.type, "sqrt");
});

test("strokes: integral with limits and absolute value", () => {
  const exact = (spec) => {
    const { strokes } = synthesizeStrokes(spec, rng(3).next, { em: 44, rot: 0, shear: 0, aniso: 0, jitter: 0, wobble: 0, drift: 0 });
    return recognizeStrokes(strokes);
  };
  const r = exact(["∫", { subsup: ["0", "1"] }, "xdx"]);
  eq(r.text, "int_(0)^(1)x d x");
  ok(r.parseable);
  const r2 = exact("2π-θ≤|x|");
  eq(r2.text, "2pi-theta<=|x|");
});

// ---------------------------------------------------------------------------------------------
// 3. honesty about ambiguity
test("strokes: a bare vertical stroke is ambiguous between 1, l and |, and is flagged", () => {
  const R = rng(99);
  for (let k = 0; k < 5; k++) {
    const em = 40;
    // an upright but wobbly stroke (a strongly slanted one is legitimately a "/")
    const strokes = distortStrokes([[[0.2, 0.72], [0.2, 0]]], R.next, { em, x: 100, y: 200, ...NEAT, rot: 2, shear: 0.03 });
    const r = recognizeStrokes(strokes, { em });
    checkContract(r);
    eq(r.symbols.length, 1);
    const s = r.symbols[0];
    ok(["1", "l", "|"].includes(s.char), s.char);
    ok(s.confidence < LOW_CONFIDENCE, `confidence ${s.confidence}`);
    ok(r.lowConfidence.includes(0), "listed in lowConfidence");
    const top3 = [s.char, ...s.alternatives.map((a) => a.char)];
    ok(["1", "l", "|"].filter((c) => top3.includes(c)).length >= 2, `alternatives ${top3}`);
  }
  // a clear "1" with its flag is not ambiguous
  const flag = VARIANTS["1"].find((v) => v.name === "flag").strokes.map((s) => s.map(([x, y]) => ({ x: 100 + x * 40, y: 200 - y * 40 })));
  const r = recognizeStrokes(flag, { em: 40 });
  eq(r.symbols[0].char, "1");
  ok(r.symbols[0].confidence >= LOW_CONFIDENCE);
});

test("strokes: text that cannot be parsed is flagged, not passed off", () => {
  const t = typeset("2+=", { em: 40, variant: "first" });
  const strokes = t.glyphs.flatMap((g) => g.strokes);
  const r = recognizeStrokes(strokes);
  eq(r.text, "2+=");
  eq(r.parseable, false);
  ok(r.parseError.message.length > 0);
  const r2 = recognizeStrokes([]);
  eq(r2.text, "");
  eq(r2.parseable, false);
});

// ---------------------------------------------------------------------------------------------
// 4. user templates
test("strokes: user-taught templates are used and survive export/import", () => {
  clearTemplates();
  // a symbol the built-in set does not know: a "k" (stem + chevron)
  const k = (dx, s) => [
    [{ x: dx, y: 100 }, { x: dx, y: 100 + 30 * s }],
    [{ x: dx + 18 * s, y: 110 }, { x: dx + 2, y: 118 }, { x: dx + 18 * s, y: 130 }],
  ];
  addTemplate("k", k(100, 1));
  addTemplate("k", k(300, 1.2));
  const r = recognizeStrokes(k(500, 1.1));
  eq(r.symbols[0].char, "k");
  const json = exportTemplates();
  clearTemplates();
  ok(recognizeStrokes(k(500, 1.1)).symbols[0].char !== "k", "gone after clear");
  const n = importTemplates(json);
  eq(n.strokes, 2);
  eq(recognizeStrokes(k(500, 1.1)).symbols[0].char, "k");
  clearTemplates();
});

// ---------------------------------------------------------------------------------------------
// 5. photos of printed math
function photo(spec, { rot = 0, noise = null, seed = 1, slant = 0 } = {}) {
  let img = renderMath(spec, { em: 40, weight: 0.08, slant, variant: "first" });
  if (rot) img = rotateImage(img, rot);
  if (noise) addNoise(img, rng(seed).next, noise);
  return img;
}
const NOISE = { sigma: 25, specks: 150, gradient: 60 };

test("photo: 3x+2=11 clean, rotated 3 degrees, and noisy", () => {
  const clean = recognizeImage(photo("3x+2=11"));
  checkContract(clean);
  eq(clean.text, "3x+2=11");
  eq(clean.lowConfidence.length, 0, "clean print is confident");
  const rot = recognizeImage(photo("3x+2=11", { rot: 3 }));
  eq(rot.text, "3x+2=11");
  ok(Math.abs(Math.abs(rot.preprocess.skew) - 3) < 1, `skew ${rot.preprocess.skew}`);
  const noisy = recognizeImage(photo("3x+2=11", { rot: -2, noise: NOISE, seed: 4 }));
  checkContract(noisy);
  eq(noisy.text, "3x+2=11");
});

test("photo: a fraction, clean, rotated and noisy", () => {
  for (const opts of [{}, { rot: 3 }, { rot: -2, noise: NOISE, seed: 9 }]) {
    const r = recognizeImage(photo({ frac: ["x+1", "2"] }, opts));
    checkContract(r);
    eq(r.text, "(x+1)/(2)", JSON.stringify(opts));
  }
});

test("photo: exponents, radicals, subscripts, dots and multi-part glyphs", () => {
  const cases = [
    [["x", { sup: "2" }, "-4=0"], "x^(2)-4=0"],
    [[{ sqrt: "x+1" }, "=3"], "sqrt(x+1)=3"],
    [["y", { sub: "1" }, "+5!"], "y_1+5!"],
    ["7.5,ij", "7.5,i j"],
    ["a÷b", "a/b"],
    ["2π-θ≤|x|", "2pi-theta<=|x|"],
  ];
  for (const [spec, want] of cases) {
    const r = recognizeImage(photo(spec));
    checkContract(r);
    eq(r.text, want);
  }
});

test("photo: dark-mode screenshot (light ink on dark paper)", () => {
  const img = photo("2x=6");
  for (let i = 0; i < img.data.length; i += 4) for (let c = 0; c < 3; c++) img.data[i + c] = 255 - img.data[i + c];
  const r = recognizeImage(img);
  ok(r.preprocess.inverted);
  eq(r.text, "2x=6");
});

test("photo: an unflagged plain stem is ambiguous and flagged", () => {
  // "1" drawn as a bare stem (no flag) next to clear digits
  const r = recognizeImage(photo(["2", { glyph: "1", variant: 1 }, "3"]));
  checkContract(r);
  const i = r.symbols.findIndex((s) => ["1", "l", "|"].includes(s.char));
  ok(i >= 0, r.text);
  ok(r.lowConfidence.includes(i), `stem confidence ${r.symbols[i].confidence}`);
});

// ---------------------------------------------------------------------------------------------
// 6. layout on exact boxes, and editable tokens
test("layout: nested fractions, powers of fractions, integral limits", () => {
  const cases = [
    [{ frac: [{ frac: ["1", "2"] }, "3"] }, "((1)/(2))/(3)"],
    [["x", { sup: [{ frac: ["1", "2"] }] }], "x^((1)/(2))"],
    [["∫", { subsup: ["0", "1"] }, "xdx"], "int_(0)^(1)x d x"],
    [["e", { sup: ["2", "x"] }], "e^(2x)"],
    [["b", { sub: "n" }, "+t"], "b_n+t"],
  ];
  for (const [spec, want] of cases) {
    const t = typeset(spec, { em: 40, variant: "first" });
    const syms = t.glyphs.map((g) => ({ char: g.char, bbox: bboxOfStrokes(g.strokes), confidence: 1 }));
    const L = analyzeLayout(syms);
    eq(L.text, want);
    ok(parses(L.text), want);
    // every symbol appears in the text map exactly once
    eq(new Set(L.map.map((m) => m.symbol)).size, syms.length, "all symbols mapped");
  }
});

test("toEditable: tokens rebuild the text and carry the uncertainty", () => {
  const R = rng(12);
  const { strokes } = synthesizeStrokes(["x", { sup: "2" }, "+1"], R.next, { em: 40, ...NEAT });
  const vertical = distortStrokes([[[0.2, 0.72], [0.2, 0]]], R.next, { em: 40, x: 200, y: 94, ...NEAT });
  const r = recognizeStrokes([...strokes, ...vertical]);
  const tokens = toEditable(r);
  eq(tokens.map((t) => t.text).join(""), r.text);
  for (const t of tokens) {
    if (t.structural) { eq(t.symbol, -1); continue; }
    eq(t.uncertain, r.symbols[t.symbol].confidence < LOW_CONFIDENCE);
    ok(Array.isArray(t.alternatives));
  }
  ok(tokens.some((t) => t.uncertain), "the bare stroke shows as uncertain");
  // π is offered to the editor as parser text
  const piStrokes = VARIANTS["π"][0].strokes.map((s) => s.map(([x, y]) => ({ x: 100 + x * 40, y: 200 - y * 40 })));
  const tp = toEditable(recognizeStrokes(piStrokes, { em: 40 }));
  eq(tp[0].text, "pi");
});
