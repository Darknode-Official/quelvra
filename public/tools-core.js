// Quelvra Tools: the pure logic behind the Tools tab (no DOM, importable in Node).
//
// Every tool turns its UI state into ordinary engine inputs (text plus options) that the worker
// solves and verifies, and turns engine results back into what the UI shows. Nothing here
// computes an answer itself, except drawing geometry (histogram bins, plot scales), which is
// approximation by nature and never shown as an exact result.

import * as X from "./engine/expr.js";
import { parse } from "./engine/parse.js";
import { toText } from "./engine/print.js";
import { simplify } from "./engine/simplify.js";

// ------------------------------------------------------------------ shared
export const TOOLS = [
  ["graph", "Graphing"],
  ["matrix", "Matrices"],
  ["units", "Units"],
  ["calc", "Calculator"],
  ["stats", "Statistics"],
  ["numtheory", "Number theory"],
  ["formulas", "Formulas"],
  ["system", "Systems"],
];
export const TOOL_IDS = TOOLS.map(([id]) => id);

const recNode = (v) => (v && v.$tree ? v.node : v && typeof v === "object" && typeof v.k === "string" ? v : null);
const recText = (v) => (v == null ? "" : typeof v === "string" ? v : v.$tree ? v.text || "" : v.k ? safeText(v) : String(v));
function safeText(u) { try { return toText(u); } catch (_) { return ""; } }
function safeSimpleText(u) { try { return toText(simplify(u)); } catch (_) { return safeText(u); } }

// What a result is worth, for the badge next to it. A failed verification never reaches the UI
// (the engine withholds it), so the states are: verified, approximate, partial, exact but not
// independently checkable, and no answer.
export function verdict(r) {
  if (!r) return { state: "none", text: "No result" };
  const answers = (r.answers || []).filter(Boolean);
  const real = answers.filter((a) => a.kind !== "none");
  const status = r.solutionStatus || "exact";
  const v = (r.verification && r.verification.status) || "not-applicable";
  if (!real.length || status === "unsolved" || status === "unsupported") {
    const why = answers.find((a) => a.label)?.label || (status === "unsupported" ? "Not supported" : "No verified answer");
    // a proven empty set is still a verified answer
    if (r.noSolution || /no (real )?solution/i.test(why)) return { state: v === "passed" ? "verified" : "exact", text: why, empty: true };
    return { state: "none", text: why };
  }
  if (status === "approximate" || real.every((a) => a.kind === "approx")) return { state: "approx", text: v === "passed" ? "Approximate, checked numerically" : "Approximate" };
  if (status === "partial") return { state: "partial", text: "Partial result" };
  if (v === "passed") return { state: "verified", text: "Verified" };
  if (v === "partial") return { state: "partial", text: "Partly verified" };
  return { state: "exact", text: "Exact" };
}

// First decimal approximation in a result ("" when there is none).
export function decimalOf(r) {
  for (const a of (r && r.answers) || []) if (a && a.approx && a.approx.value) return String(a.approx.value);
  return "";
}
export function exactAnswers(r) {
  return ((r && r.answers) || []).filter((a) => a && a.kind !== "none" && a.kind !== "approx" && (a.tree || a.text));
}
export const answerText = (a) => (a ? (a.tree ? recText(a.tree) : a.text || a.label || "") : "");

// A plain JS number from a result tree record, text or number (plotting only).
export function floatOf(v) {
  if (typeof v === "number") return v;
  if (typeof v === "string") {
    const n = Number(v);
    if (Number.isFinite(n)) return n;
    try { return evalFloat(parse(v)); } catch (_) { return NaN; }
  }
  const node = recNode(v);
  return node ? evalFloat(node) : NaN;
}
// Small double evaluator for constant trees (numbers, pi, e, + * ^, sqrt and the usual functions).
const F1 = { sin: Math.sin, cos: Math.cos, tan: Math.tan, asin: Math.asin, acos: Math.acos, atan: Math.atan, ln: Math.log, exp: Math.exp, abs: Math.abs, sqrt: Math.sqrt, cbrt: Math.cbrt, sinh: Math.sinh, cosh: Math.cosh, tanh: Math.tanh, floor: Math.floor, ceil: Math.ceil };
export function evalFloat(u, env = {}) {
  switch (u.k) {
    case "num": return Number(u.v.n) / Number(u.v.d);
    case "const": return u.name === "pi" ? Math.PI : u.name === "e" ? Math.E : u.name === "oo" ? Infinity : NaN;
    case "sym": return u.name in env ? env[u.name] : NaN;
    case "add": return u.args.reduce((s, a) => s + evalFloat(a, env), 0);
    case "mul": return u.args.reduce((s, a) => s * evalFloat(a, env), 1);
    case "pow": {
      const b = evalFloat(u.args[0], env), e = evalFloat(u.args[1], env);
      // odd roots of negatives are real: (-8)^(1/3) = -2, (-8)^(2/3) = 4
      if (b < 0 && !Number.isInteger(e)) {
        for (let d = 3; d < 100; d += 2) {
          const n = Math.round(e * d);
          if (Math.abs(e * d - n) < 1e-9) return (n % 2 === 0 ? 1 : -1) * Math.pow(-b, e);
        }
      }
      return Math.pow(b, e);
    }
    case "fn": {
      if (u.name === "log") return u.args.length === 1 ? Math.log10(evalFloat(u.args[0], env)) : Math.log(evalFloat(u.args[1], env)) / Math.log(evalFloat(u.args[0], env));
      const f = F1[u.name];
      return f && u.args.length === 1 ? f(evalFloat(u.args[0], env)) : NaN;
    }
    default: return NaN;
  }
}

// Human formatting of a double for tables and axes (not for exact answers).
export function fmt(v, sig = 6) {
  if (!Number.isFinite(v)) return v > 0 ? "inf" : v < 0 ? "-inf" : "undefined";
  if (v === 0) return "0";
  const a = Math.abs(v);
  if (a >= 1e9 || a < 1e-5) return v.toExponential(Math.max(0, sig - 1)).replace(/\.?0+e/, "e").replace("e+", "e");
  return String(+v.toPrecision(sig));
}

// A decimal or fraction typed by a person, as exact engine text ("" when invalid).
// Accepts 12, -3.5, .5, 1e-3, 2.5E4, 3/4, -1/3.
const NUM_RE = /^[-+]?(?:\d+\.?\d*|\.\d+)(?:[eE][-+]?\d+)?$/;
export function exactNumberText(s) {
  s = String(s ?? "").trim().replace(/[−–]/g, "-").replace(/\s+/g, "");
  if (!s) return "";
  const fr = s.match(/^([-+]?\d+)\/(\d+)$/);
  if (fr) return fr[2] === "0" || /^0+$/.test(fr[2]) ? "" : `${fr[1].replace(/^\+/, "")}/${fr[2]}`;
  if (!NUM_RE.test(s)) return "";
  const m = s.match(/^([-+]?)(\d*\.?\d*)(?:[eE]([-+]?\d+))?$/);
  const sign = m[1] === "-" ? "-" : "";
  let mant = m[2];
  if (mant.startsWith(".")) mant = "0" + mant;
  if (mant.endsWith(".")) mant = mant.slice(0, -1);
  if (!m[3]) return sign + mant;
  // move the decimal point instead of emitting 10^k so the engine sees a plain exact decimal
  let [ip, fp = ""] = mant.split(".");
  let e = parseInt(m[3], 10);
  if (Math.abs(e) > 400) return "";
  if (e > 0) { fp = fp.padEnd(e, "0"); ip += fp.slice(0, e); fp = fp.slice(e); }
  else if (e < 0) { ip = ip.padStart(-e + 1, "0"); fp = ip.slice(ip.length + e) + fp; ip = ip.slice(0, ip.length + e); }
  ip = ip.replace(/^0+(?=\d)/, "") || "0";
  fp = fp.replace(/0+$/, "");
  return sign + ip + (fp ? "." + fp : "");
}

// ------------------------------------------------------------------ matrices
export const MAX_DIM = 8;
export function makeGrid(rows, cols, fill = "") {
  return Array.from({ length: rows }, () => Array.from({ length: cols }, () => fill));
}
export function resizeGrid(grid, rows, cols) {
  rows = Math.max(1, Math.min(MAX_DIM, rows | 0));
  cols = Math.max(1, Math.min(MAX_DIM, cols | 0));
  return Array.from({ length: rows }, (_, i) => Array.from({ length: cols }, (_, j) => (grid[i] && grid[i][j] != null ? grid[i][j] : "")));
}
// A cell holds any scalar expression (2, -1/3, sqrt(2), a); empty means 0.
const CELL_BAD = /[\[\];=<>{}]|,/;
export function cellError(s) {
  s = String(s ?? "").trim();
  if (!s) return "";
  if (CELL_BAD.test(s)) return "A cell holds one number or expression";
  try { parse(s); } catch (e) { return (e && e.message) || "Cannot read this entry"; }
  return "";
}
export function gridErrors(grid) {
  const out = [];
  grid.forEach((row, i) => row.forEach((c, j) => { const e = cellError(c); if (e) out.push({ row: i, col: j, message: e }); }));
  return out;
}
export function matrixText(grid) {
  return "[" + grid.map((row) => "[" + row.map((c) => (String(c ?? "").trim() || "0")).join(", ") + "]").join(", ") + "]";
}
// Paste from a spreadsheet or text: rows on lines (or "[[..],[..]]"), cells split by tabs, commas or spaces.
export function parseGridText(text) {
  const s = String(text || "").trim();
  if (!s) return null;
  if (/^\[\s*\[/.test(s)) {
    const rows = s.replace(/^\[\s*\[/, "").replace(/\]\s*\]$/, "").split(/\]\s*,\s*\[/);
    const grid = rows.map((r) => r.split(",").map((c) => c.trim()));
    return rectangular(grid) ? grid : null;
  }
  const lines = s.split(/\r?\n|;/).map((l) => l.trim()).filter(Boolean);
  const grid = lines.map((l) => (/\t/.test(l) ? l.split("\t") : /,/.test(l) ? l.split(",") : l.split(/\s+/)).map((c) => c.trim()));
  return rectangular(grid) && grid.length <= MAX_DIM && grid[0].length <= MAX_DIM ? grid : null;
}
const rectangular = (g) => g.length > 0 && g.every((r) => r.length === g[0].length) && g[0].length > 0;

export const MATRIX_OPS = [
  ["det", "Determinant", "A"], ["inv", "Inverse", "A"], ["transpose", "Transpose", "A"], ["rank", "Rank", "A"],
  ["rref", "Reduced row echelon form", "A"], ["eigenvalues", "Eigenvalues", "A"], ["trace", "Trace", "A"],
  ["mul", "A times B", "AB"], ["add", "A plus B", "AB"], ["sub", "A minus B", "AB"], ["pow", "A to a power", "An"], ["solve", "Solve A x = b", "Ab"],
];
// Build the engine request for one operation, or { error } when the shapes do not fit.
export function matrixRequest(op, A, B, n) {
  const [ar, ac] = [A.length, A[0].length];
  const square = ar === ac;
  const ta = matrixText(A);
  const need = (cond, msg) => (cond ? null : { error: msg });
  switch (op) {
    case "det": case "inv": case "eigenvalues": case "trace":
      return need(square, "This operation needs a square matrix A") || { input: `${op}(${ta})` };
    case "transpose": case "rank": case "rref":
      return { input: `${op}(${ta})` };
    case "mul": {
      const e = need(ac === B.length, `A has ${ac} column${ac > 1 ? "s" : ""} but B has ${B.length} row${B.length > 1 ? "s" : ""}`);
      return e || { input: `${ta} * ${matrixText(B)}` };
    }
    case "add": case "sub": {
      const e = need(ar === B.length && ac === B[0].length, "A and B must have the same size");
      return e || { input: `${ta} ${op === "add" ? "+" : "-"} ${matrixText(B)}` };
    }
    case "pow": {
      const k = String(n ?? "").trim();
      if (!/^-?\d{1,3}$/.test(k)) return { error: "The power must be a whole number from -999 to 999" };
      return need(square, "Powers need a square matrix A") || { input: `${ta}^(${k})` };
    }
    case "solve": {
      // b is the first column of B; the system is written out row by row with unknowns x1..xn
      if (B.length !== ar) return { error: `b needs ${ar} row${ar > 1 ? "s" : ""}, one per row of A` };
      const vars = Array.from({ length: ac }, (_, j) => `x_${j + 1}`);
      const eqs = A.map((row, i) => row.map((c, j) => `(${String(c).trim() || "0"})*${vars[j]}`).join(" + ") + ` = ${String(B[i][0]).trim() || "0"}`);
      return { input: eqs.join("; "), options: { variable: vars }, vars };
    }
    default: return { error: "Unknown operation" };
  }
}

// ------------------------------------------------------------------ units
// Every unit carries an exact factor to its category's base unit. Units the engine knows by
// symbol ("sym") are converted by the engine's own unit system; any pair involving a unit it
// does not know is converted by exact arithmetic on these factors, which the engine evaluates.
// Temperature is affine and only uses engine symbols.
export const UNIT_CATEGORIES = [
  { id: "length", label: "Length", base: "m", units: [
    ["mm", "millimetre", "mm", "1/1000"], ["cm", "centimetre", "cm", "1/100"], ["m", "metre", "m", "1"], ["km", "kilometre", "km", "1000"],
    ["um", "micrometre", "um", "1/1000000"], ["in", "inch", "in", "0.0254"], ["ft", "foot", "ft", "0.3048"], ["yd", "yard", "yd", "0.9144"],
    ["mi", "mile", "mi", "1609.344"], ["nmi", "nautical mile", "nmi", "1852"],
  ] },
  { id: "mass", label: "Mass", base: "kg", units: [
    ["mg", "milligram", "mg", "1/1000000"], ["g", "gram", "g", "1/1000"], ["kg", "kilogram", "kg", "1"], ["t", "tonne", "t", "1000"],
    ["oz", "ounce", "oz", "0.45359237/16"], ["lb", "pound", "lb", "0.45359237"], ["st", "stone", null, "14*0.45359237"], ["ton", "short ton (US)", "ton", "2000*0.45359237"],
  ] },
  { id: "time", label: "Time", base: "s", units: [
    ["ms", "millisecond", "ms", "1/1000"], ["s", "second", "s", "1"], ["min", "minute", "min", "60"], ["h", "hour", "h", "3600"],
    ["day", "day", "day", "86400"], ["week", "week", "week", "604800"], ["yr", "Julian year (365.25 days)", "yr", "31557600"],
  ] },
  { id: "speed", label: "Speed", base: "m/s", units: [
    ["m/s", "metre per second", "m/s", "1"], ["km/h", "kilometre per hour", "km/h", "1000/3600"], ["mph", "mile per hour", "mph", "1609.344/3600"],
    ["knot", "knot", "knot", "1852/3600"], ["ft/s", "foot per second", "ft/s", "0.3048"],
  ] },
  { id: "temperature", label: "Temperature", base: "K", units: [
    ["degC", "degree Celsius", "degC", null], ["degF", "degree Fahrenheit", "degF", null], ["K", "kelvin", "K", null],
  ] },
  { id: "area", label: "Area", base: "m^2", units: [
    ["mm^2", "square millimetre", "mm^2", "1/1000000"], ["cm^2", "square centimetre", "cm^2", "1/10000"], ["m^2", "square metre", "m^2", "1"],
    ["ha", "hectare", "ha", "10000"], ["km^2", "square kilometre", "km^2", "1000000"], ["in^2", "square inch", "in^2", "0.0254^2"],
    ["ft^2", "square foot", "ft^2", "0.3048^2"], ["yd^2", "square yard", "yd^2", "0.9144^2"], ["acre", "acre", null, "4840*0.9144^2"],
    ["mi^2", "square mile", "mi^2", "1609.344^2"],
  ] },
  { id: "volume", label: "Volume", base: "m^3", units: [
    ["mL", "millilitre", "mL", "1/1000000"], ["cm^3", "cubic centimetre", "cm^3", "1/1000000"], ["L", "litre", "L", "1/1000"], ["m^3", "cubic metre", "m^3", "1"],
    ["in^3", "cubic inch", "in^3", "0.0254^3"], ["ft^3", "cubic foot", "ft^3", "0.3048^3"], ["floz", "US fluid ounce", null, "231*0.0254^3/128"],
    ["cup", "US cup", null, "231*0.0254^3/16"], ["qt", "US quart", null, "231*0.0254^3/4"], ["gal", "US gallon", "gal", "231*0.0254^3"],
  ] },
  { id: "energy", label: "Energy", base: "J", units: [
    ["J", "joule", "J", "1"], ["kJ", "kilojoule", "kJ", "1000"], ["cal", "calorie (thermochemical)", "cal", "4.184"], ["kcal", "kilocalorie", "kcal", "4184"],
    ["Wh", "watt hour", "Wh", "3600"], ["kWh", "kilowatt hour", "kWh", "3600000"], ["eV", "electronvolt", "eV", "1.602176634e-19"], ["BTU", "British thermal unit (IT)", null, "1055.05585262"],
  ] },
  { id: "pressure", label: "Pressure", base: "Pa", units: [
    ["Pa", "pascal", "Pa", "1"], ["kPa", "kilopascal", "kPa", "1000"], ["bar", "bar", "bar", "100000"], ["atm", "standard atmosphere", "atm", "101325"],
    ["psi", "pound per square inch", "psi", "0.45359237*9.80665/0.0254^2"], ["mmHg", "millimetre of mercury", "mmHg", "133.322387415"], ["torr", "torr", "torr", "101325/760"],
  ] },
  { id: "data", label: "Data", base: "bit", units: [
    ["bit", "bit", null, "1"], ["B", "byte", null, "8"], ["kB", "kilobyte (1000 B)", null, "8*10^3"], ["KiB", "kibibyte (1024 B)", null, "8*2^10"],
    ["MB", "megabyte", null, "8*10^6"], ["MiB", "mebibyte", null, "8*2^20"], ["GB", "gigabyte", null, "8*10^9"], ["GiB", "gibibyte", null, "8*2^30"],
    ["TB", "terabyte", null, "8*10^12"], ["TiB", "tebibyte", null, "8*2^40"],
  ] },
].map((c) => ({ ...c, units: c.units.map(([id, label, sym, factor]) => ({ id, label, sym, factor })) }));

export const unitCategory = (id) => UNIT_CATEGORIES.find((c) => c.id === id) || null;
export function findUnit(cat, id) { const c = typeof cat === "string" ? unitCategory(cat) : cat; return c ? c.units.find((u) => u.id === id) || null : null; }
const factorText = (f) => f.replace(/(\d(?:\.\d+)?)e(-?\d+)/g, "$1*10^($2)");

// The engine request for "value from -> to" ({ input, via: "units" | "factors" } or { error }).
export function conversionRequest(catId, fromId, toId, value) {
  const cat = unitCategory(catId);
  const from = findUnit(cat, fromId), to = findUnit(cat, toId);
  if (!cat || !from || !to) return { error: "Choose both units" };
  const v = exactNumberText(value);
  if (!v) return { error: "Enter a number, for example 12.5 or 3/4" };
  // the engine's unit reader takes a plain decimal; a fraction goes through the exact factors
  if (from.sym && to.sym && (!v.includes("/") || !from.factor || !to.factor)) {
    if (v.includes("/")) return { error: "Enter temperatures as decimals, for example 36.6" };
    return { input: `${v} ${from.sym} to ${to.sym}`, via: "units", value: v };
  }
  if (!from.factor || !to.factor) return { error: "These units cannot be converted" };
  return { input: `(${v}) * (${factorText(from.factor)}) / (${factorText(to.factor)})`, via: "factors", value: v };
}

// ------------------------------------------------------------------ scientific calculator
const TRIG = new Set(["sin", "cos", "tan", "cot", "sec", "csc"]);
const ATRIG = new Set(["asin", "acos", "atan", "acot", "asec", "acsc"]);
// Calculator text -> engine text. "Ans" and "M" are replaced by the previous answer and memory;
// in degree mode trig arguments are multiplied by pi/180 and inverse trig results by 180/pi.
export function calcInput(src, { angle = "rad", ans = "", memory = "" } = {}) {
  let s = String(src || "").trim();
  if (!s) return { error: "Nothing to evaluate" };
  s = s.replace(/×/g, "*").replace(/÷/g, "/").replace(/−/g, "-").replace(/π/g, "pi").replace(/√/g, "sqrt");
  if (/\bAns\b/.test(s)) { if (!ans) return { error: "There is no previous answer yet" }; s = s.replace(/\bAns\b/g, `(${ans})`); }
  if (/\bMR\b/.test(s)) { if (!memory) return { error: "Memory is empty" }; s = s.replace(/\bMR\b/g, `(${memory})`); }
  let tree;
  try { tree = parse(s); } catch (e) { return { error: (e && e.message) || "Cannot read the input", pos: e && e.pos }; }
  if (X.freeSymbols(tree).size) return { error: `Unknown name ${[...X.freeSymbols(tree)][0]}: the calculator works with numbers` };
  if (angle === "deg") tree = toDegrees(tree);
  return { input: safeText(tree) || s };
}
export function toDegrees(tree) {
  const k = X.mul(X.PI, X.pow(X.num(180), X.NEG_ONE));
  const inv = X.mul(X.num(180), X.pow(X.PI, X.NEG_ONE));
  return X.mapTree(tree, (u) => {
    if (u.k !== "fn" || u.args.length !== 1) return u;
    if (TRIG.has(u.name)) return X.fn(u.name, X.mul(u.args[0], k));
    if (ATRIG.has(u.name)) return X.mul(inv, u);
    return u;
  });
}
// Keypad: [label, insert, aria label, class]. Inserts use "|" for the caret position.
export const CALC_KEYS = [
  ["sin", "sin(|)", "sine"], ["cos", "cos(|)", "cosine"], ["tan", "tan(|)", "tangent"], ["(", "(", "open bracket"], [")", ")", "close bracket"],
  ["asin", "asin(|)", "arcsine"], ["acos", "acos(|)", "arccosine"], ["atan", "atan(|)", "arctangent"], ["x²", "^2", "squared"], ["xʸ", "^(|)", "power"],
  ["ln", "ln(|)", "natural log"], ["log", "log(|)", "log base 10"], ["√", "sqrt(|)", "square root"], ["n!", "!", "factorial"], ["π", "pi", "pi"],
  ["7", "7"], ["8", "8"], ["9", "9"], ["÷", " / ", "divide", "op"], ["e", "e", "Euler's number"],
  ["4", "4"], ["5", "5"], ["6", "6"], ["×", " * ", "times", "op"], ["Ans", "Ans", "previous answer"],
  ["1", "1"], ["2", "2"], ["3", "3"], ["−", " - ", "minus", "op"], ["EXP", "*10^(|)", "times ten to the power"],
  ["0", "0"], [".", ".", "decimal point"], ["%", "/100", "percent"], ["+", " + ", "plus", "op"], ["=", "=", "evaluate", "eq"],
];
export function insertTemplate(value, start, end, template) {
  const sel = value.slice(start, end);
  const i = template.indexOf("|");
  const text = i < 0 ? template : template.slice(0, i) + sel + template.slice(i + 1);
  const caret = start + (i < 0 ? text.length : i + sel.length);
  return { value: value.slice(0, start) + text + value.slice(end), caret };
}

// ------------------------------------------------------------------ statistics
// A list of numbers typed or pasted: separated by commas, semicolons, spaces, tabs or new lines.
export function parseData(text) {
  const tokens = String(text || "").replace(/[−]/g, "-").split(/[\s,;]+/).map((t) => t.trim()).filter(Boolean);
  const values = [], bad = [];
  for (const t of tokens) { const v = exactNumberText(t); if (v) values.push(v); else bad.push(t); }
  return { values, bad, floats: values.map((v) => floatOf(v)) };
}
// x,y pairs, one per line ("1, 2", "1 2", "1\t2"); a header line of words is skipped.
export function parsePairs(text) {
  const xs = [], ys = [], bad = [];
  const lines = String(text || "").split(/\r?\n/).map((l) => l.trim()).filter(Boolean);
  lines.forEach((l, i) => {
    const parts = l.replace(/[()]/g, "").split(/[\s,;]+/).filter(Boolean);
    const x = exactNumberText(parts[0]), y = exactNumberText(parts[1]);
    if (parts.length === 2 && x && y) { xs.push(x); ys.push(y); }
    else if (!(i === 0 && parts.every((p) => /^[a-z_]+$/i.test(p)))) bad.push(i + 1);
  });
  return { xs, ys, bad };
}
const list = (vs) => vs.join(", ");
export function statsRequests(values) {
  if (!values.length) return [];
  const l = list(values);
  const out = [["mean", `mean(${l})`], ["median", `median(${l})`], ["sum", values.map((v) => `(${v})`).join(" + ")]];
  if (values.length >= 2) out.push(["mode", `mode(${l})`], ["stdev", `stdev(${l})`], ["range", `datarange(${l})`]);
  if (values.length >= 3) out.push(["quartiles", `quartiles(${l})`], ["iqr", `iqr(${l})`]);
  return out;
}
export function regressionRequests(xs, ys) {
  return [["linreg", `linreg([${list(xs)}], [${list(ys)}])`], ["corr", `corr([${list(xs)}], [${list(ys)}])`]];
}
// Sturges' rule bins over [min, max]; the last bin is closed on the right.
export function histogramBins(nums, k) {
  const v = nums.filter(Number.isFinite);
  if (!v.length) return [];
  let lo = Math.min(...v), hi = Math.max(...v);
  if (lo === hi) { lo -= 0.5; hi += 0.5; }
  const n = Math.max(1, Math.min(30, k || Math.ceil(Math.log2(v.length) + 1)));
  const w = (hi - lo) / n;
  const bins = Array.from({ length: n }, (_, i) => ({ lo: lo + i * w, hi: i === n - 1 ? hi : lo + (i + 1) * w, count: 0 }));
  for (const x of v) bins[Math.min(n - 1, Math.floor((x - lo) / w))].count++;
  return bins;
}
// Box plot geometry from the engine's quartiles (floats) and the data; whiskers at 1.5 IQR.
export function boxPlot(nums, q1, q2, q3) {
  const v = nums.filter(Number.isFinite).sort((a, b) => a - b);
  const iqr = q3 - q1;
  const loF = q1 - 1.5 * iqr, hiF = q3 + 1.5 * iqr;
  const inside = v.filter((x) => x >= loF && x <= hiF);
  return { q1, q2, q3, whiskerLo: inside.length ? inside[0] : q1, whiskerHi: inside.length ? inside[inside.length - 1] : q3, outliers: v.filter((x) => x < loF || x > hiF), min: v[0], max: v[v.length - 1] };
}

// ------------------------------------------------------------------ number theory
// A whole number, possibly written as an expression (2^61 - 1); digits separators are allowed.
export function intText(s) {
  s = String(s ?? "").trim().replace(/[−]/g, "-").replace(/(\d)[ _,](?=\d{3}\b)/g, "$1");
  if (!s) return "";
  if (/^[-+]?\d+$/.test(s)) return s.replace(/^\+/, "");
  if (/^[\d\s+\-*^()!]+$/.test(s)) return s;
  return "";
}
const DIGITS = "0123456789abcdefghijklmnopqrstuvwxyz";
export function digitsError(digits, base) {
  const d = String(digits || "").trim().toLowerCase().replace(/^-/, "");
  if (!d) return "Enter the digits";
  if (!(base >= 2 && base <= 36)) return "The base must be from 2 to 36";
  for (const ch of d) { const v = DIGITS.indexOf(ch); if (v < 0 || v >= base) return `The digit ${ch.toUpperCase()} is not allowed in base ${base}`; }
  return "";
}
// Digits in base b -> an exact arithmetic expression the engine evaluates (sum of d_i b^i).
export function fromBaseExpr(digits, base) {
  const raw = String(digits).trim().toLowerCase();
  const neg = raw.startsWith("-");
  const d = raw.replace(/^-/, "").replace(/^0+(?=.)/, "");
  const terms = [];
  const n = d.length;
  for (let i = 0; i < n; i++) {
    const v = DIGITS.indexOf(d[i]);
    if (!v) continue;
    const e = n - 1 - i;
    terms.push(e === 0 ? String(v) : `${v === 1 ? "" : v + "*"}${base}^${e}`);
  }
  const body = terms.length ? terms.join(" + ") : "0";
  return neg ? `-(${body})` : body;
}
export function ntRequest(op, a, b, c) {
  const A = intText(a), B = intText(b), C = intText(c);
  const needs = (...xs) => xs.every(Boolean);
  switch (op) {
    case "factor": return needs(A) ? { input: `factorint(${A})` } : { error: "Enter a whole number" };
    case "gcd": case "lcm": {
      const nums = String(a || "").split(/[\s,;]+/).map(intText).filter(Boolean);
      return nums.length >= 2 ? { input: `${op}(${nums.join(", ")})` } : { error: "Enter at least two whole numbers" };
    }
    case "modinv": return needs(A, B) ? { input: `(${A}) x = 1 mod ${B}`, modulus: B } : { error: "Enter a and the modulus m" };
    case "powmod": return needs(A, B, C) ? { input: `powmod(${A}, ${B}, ${C})` } : { error: "Enter the base, the exponent and the modulus" };
    case "tobase": {
      const base = Number(B);
      if (!needs(A) || !/^-?\d+$/.test(A)) return { error: "Enter a whole number in base 10" };
      if (!(base >= 2 && base <= 36)) return { error: "The base must be from 2 to 36" };
      return { input: `tobase(${A}, ${base})` };
    }
    case "frombase": {
      const base = Number(B);
      const err = digitsError(a, base);
      return err ? { error: err } : { input: fromBaseExpr(a, base) };
    }
    default: return { error: "Unknown operation" };
  }
}
// The residue r in an engine answer "m k + r" (a congruence solution), as a canonical 0 <= r < m.
export function residueOf(v, m) {
  const node = recNode(v);
  const M = BigInt(m);
  if (!node || M <= 0n) return null;
  const terms = node.k === "add" ? node.args : [node];
  let r = 0n;
  const constInt = (t) => {
    if (t.k === "num") return t.v.d === 1n ? t.v.n : null;
    if (t.k === "mul") { let p = 1n; for (const a of t.args) { const v = constInt(a); if (v === null) return null; p *= v; } return p; }
    return null;
  };
  for (const t of terms) {
    if (!X.freeSymbols(t).size) { const v = constInt(t); if (v === null) return null; r += v; continue; }
    // the free part must be a multiple of the modulus times the integer parameter: m k
    const c = t.k === "mul" && t.args.length === 2 && t.args[0].k === "num" && t.args[1].k === "sym" ? constInt(t.args[0]) : t.k === "sym" ? 1n : null;
    if (c === null || c % M !== 0n) return null;
  }
  return ((r % M) + M) % M;
}
// A primality certificate as indented lines for display.
export function certificateLines(c, depth = 0, out = []) {
  if (!c) return out;
  const pad = "  ".repeat(depth);
  switch (c.type) {
    case "deterministic-mr": out.push(`${pad}${c.n} is prime: deterministic Miller-Rabin (bases 2 to 41 are proven sufficient below 3.317e24)`); break;
    case "lucas-lehmer": out.push(`${pad}${c.n} = 2^${c.p} - 1 is prime: the Lucas-Lehmer test passes and the exponent ${c.p} is prime`); certificateLines(c.pCert, depth + 1, out); break;
    case "pocklington":
      out.push(`${pad}${c.n} is prime: Pocklington certificate with n - 1 divisible by F = ${c.F}, F^2 > n`);
      for (const w of c.witnesses || []) out.push(`${pad}  prime q = ${w.q}: witness a = ${w.a} has a^(n-1) = 1 mod n and gcd(a^((n-1)/q) - 1, n) = 1`);
      for (const f of c.factors || []) certificateLines(f, depth + 1, out);
      break;
    default: out.push(`${pad}${c.n}: ${c.type}`);
  }
  return out;
}

// ------------------------------------------------------------------ equation systems
export function parseUnknowns(s) {
  const names = String(s || "").split(/[\s,;]+/).map((t) => t.trim()).filter(Boolean);
  const bad = names.filter((n) => !/^(?:[a-zA-Z](?:_\w+)?|theta|alpha|beta|gamma|lambda|mu|phi)$/.test(n));
  return { names: [...new Set(names)], bad };
}
export function systemRequest(lines, unknownsText) {
  const eqs = lines.map((l) => String(l || "").trim()).filter(Boolean);
  if (!eqs.length) return { error: "Add at least one equation" };
  const noEq = eqs.findIndex((e) => !/=|<|>/.test(e));
  if (noEq >= 0) return { error: `Equation ${noEq + 1} has no equals sign` };
  const { names, bad } = parseUnknowns(unknownsText);
  if (bad.length) return { error: `${bad[0]} is not a variable name` };
  const input = eqs.join("; ");
  return names.length ? { input, options: { variable: names.length === 1 ? names[0] : names } } : { input, options: {} };
}
// Unknowns to suggest: the free symbols of the equations, x y z first.
export function suggestUnknowns(lines) {
  const seen = new Set();
  for (const l of lines) {
    try { for (const s of X.freeSymbols(parse(String(l)))) seen.add(s); } catch (_) { /* skip lines that do not parse yet */ }
  }
  const pref = ["x", "y", "z", "w", "t", "u", "v"];
  const named = [...seen];
  const main = pref.filter((p) => seen.has(p));
  return (main.length ? main : named.sort()).slice(0, 8);
}

// ------------------------------------------------------------------ graphing
export const GRAPH_EXAMPLES = ["x^2 - 2", "sin(x)", "(cos(3t), sin(2t))", "r = 1 + cos(theta)", "x^2 + y^2 = 9"];
// Kind of a plot row from its parsed tree, via graph.js classifyPlot (passed in to keep this file DOM-free).
export function rowKind(cls) {
  if (!cls) return "none";
  return cls.type === "function" ? (cls.var === "x" ? "function" : "function-other") : cls.type;
}
// Engine questions for the analysis: zeros and extrema of each y = f(x), intersections of pairs.
export function analysisRequests(fns) {
  const out = [];
  fns.forEach((f, i) => {
    out.push({ key: `zeros:${i}`, kind: "zero", rows: [i], input: `zeros(${f.text})` });
    out.push({ key: `extrema:${i}`, kind: "extremum", rows: [i], input: `extrema(${f.text})` });
  });
  for (let i = 0; i < fns.length; i++) for (let j = i + 1; j < fns.length; j++) {
    out.push({ key: `meet:${i}:${j}`, kind: "intersection", rows: [i, j], input: `${fns[i].text} = ${fns[j].text}`, options: { variable: "x" } });
  }
  return out;
}
// Points from an analysis result. General answers (x = k pi) are expanded for integer k inside
// [xmin, xmax]. Each point says whether it is exact-and-verified or approximate.
export function pointsFromResult(req, r, fnAt, xmin, xmax) {
  const pts = [];
  if (!r) return pts;
  const verified = r.verification && r.verification.status === "passed";
  const add = (x, y, exact, text) => {
    if (!Number.isFinite(x) || x < xmin - 1e-9 || x > xmax + 1e-9) return;
    if (!Number.isFinite(y)) y = fnAt(x);
    if (!Number.isFinite(y)) return;
    pts.push({ x, y, kind: req.kind, rows: req.rows, status: exact && verified ? "verified" : "approximate", text: text || fmt(x), label: "" });
  };
  for (const a of r.answers || []) {
    if (!a || a.kind === "none") continue;
    if (a.kind === "approx" && a.approx) { add(Number(a.approx.value), NaN, false, "≈ " + a.approx.value); continue; }
    const node = recNode(a.tree);
    if (!node) continue;
    if (a.kind === "general") {
      const k = a.param || "k";
      const f = (kv) => evalFloat(node, { [k]: kv });
      const x0 = f(0), step = f(1) - x0;
      if (!Number.isFinite(x0) || !Number.isFinite(step)) continue;
      if (Math.abs(step) < 1e-12) { add(x0, NaN, true, recText(a.tree)); continue; }
      const k0 = Math.ceil((xmin - x0) / Math.abs(step)) * Math.sign(step), k1 = Math.floor((xmax - x0) / Math.abs(step)) * Math.sign(step);
      const [ka, kb] = [Math.min(k0, k1), Math.max(k0, k1)];
      for (let kv = ka, n = 0; kv <= kb && n < 60; kv++, n++) add(f(kv), NaN, true, safeSimpleText(X.subs(node, { [k]: X.num(kv) })) || fmt(f(kv)));
      continue;
    }
    const before = pts.length;
    if (node.k === "tuple" && node.args.length === 2) add(evalFloat(node.args[0]), evalFloat(node.args[1]), true, recText(a.tree));
    else if (a.kind === "exact" && !X.freeSymbols(node).size) add(evalFloat(node), NaN, true, recText(a.tree));
    if (pts.length > before) {
      const p = pts[pts.length - 1];
      p.label = a.label && /max/i.test(a.label) ? "max" : a.label && /min/i.test(a.label) ? "min" : "";
      if (a.approx && a.approx.value) p.decimal = String(a.approx.value);
    }
  }
  return pts;
}
// x values for a table: start, start + step, ... as exact engine text.
export function tableXs(start, step, count) {
  const s = exactNumberText(start), d = exactNumberText(step);
  const n = Math.max(1, Math.min(50, Number(count) | 0));
  if (!s || !d) return null;
  return Array.from({ length: n }, (_, i) => (i === 0 ? s : `${s} + ${i}*(${d})`));
}
// Engine text for f evaluated at x = xText (the tree is substituted, then printed).
export function substituteText(tree, v, xText) {
  try { return safeText(X.subs(tree, { [v]: parse(xText) })); } catch (_) { return ""; }
}

// ------------------------------------------------------------------ formula sheet
// [category, name, formula as shown, example the solver can run]
export const FORMULAS = [
  ["Algebra", "Quadratic formula", "x = (-b +- sqrt(b^2 - 4ac)) / (2a)", "2x^2 - 3x - 5 = 0"],
  ["Algebra", "Difference of squares", "a^2 - b^2 = (a - b)(a + b)", "factor(x^2 - 49)"],
  ["Algebra", "Perfect square", "(a + b)^2 = a^2 + 2ab + b^2", "expand((x + 3)^2)"],
  ["Algebra", "Sum of cubes", "a^3 + b^3 = (a + b)(a^2 - ab + b^2)", "factor(x^3 + 8)"],
  ["Algebra", "Exponent rules", "a^m a^n = a^(m + n),  (a^m)^n = a^(mn)", "simplify(x^3 * x^5)"],
  ["Algebra", "Logarithm of a product", "log(ab) = log(a) + log(b)", "ln(x) + ln(x + 1) = ln(6)"],
  ["Algebra", "Change of base", "log_b(x) = ln(x) / ln(b)", "log_2(x) = 5"],
  ["Algebra", "Arithmetic series", "S_n = n (a_1 + a_n) / 2", "sum(k, k, 1, 100)"],
  ["Algebra", "Geometric series", "S_n = a (1 - r^n) / (1 - r)", "sum(3 * 2^k, k, 0, 9)"],
  ["Algebra", "Binomial theorem", "(a + b)^n = sum(binomial(n, k) a^(n - k) b^k, k, 0, n)", "expand((x + 1)^5)"],
  ["Trigonometry", "Pythagorean identity", "sin(x)^2 + cos(x)^2 = 1", "simplify(sin(x)^2 + cos(x)^2)"],
  ["Trigonometry", "Double angle (sine)", "sin(2x) = 2 sin(x) cos(x)", "sin(2x) = cos(x)"],
  ["Trigonometry", "Double angle (cosine)", "cos(2x) = cos(x)^2 - sin(x)^2 = 1 - 2 sin(x)^2", "cos(2x) = 1/2"],
  ["Trigonometry", "Tangent", "tan(x) = sin(x) / cos(x)", "tan(x) = 1"],
  ["Trigonometry", "Angle sum (sine)", "sin(a + b) = sin(a) cos(b) + cos(a) sin(b)", "sin(pi/4 + pi/6)"],
  ["Trigonometry", "Angle sum (cosine)", "cos(a + b) = cos(a) cos(b) - sin(a) sin(b)", "cos(pi/3 + pi/4)"],
  ["Trigonometry", "Law of cosines", "c^2 = a^2 + b^2 - 2ab cos(C)", "c^2 = 5^2 + 7^2 - 2*5*7*cos(pi/3)"],
  ["Trigonometry", "Law of sines", "a / sin(A) = b / sin(B) = c / sin(C)", "a / sin(pi/6) = 10 / sin(pi/4)"],
  ["Derivatives", "Power rule", "d/dx x^n = n x^(n - 1)", "diff(x^7, x)"],
  ["Derivatives", "Product rule", "(f g)' = f' g + f g'", "diff(x^2 sin(x), x)"],
  ["Derivatives", "Quotient rule", "(f / g)' = (f' g - f g') / g^2", "diff(sin(x)/x, x)"],
  ["Derivatives", "Chain rule", "(f(g(x)))' = f'(g(x)) g'(x)", "diff(sin(x^2), x)"],
  ["Derivatives", "Exponential and log", "d/dx e^x = e^x,  d/dx ln(x) = 1/x", "diff(e^(3x) ln(x), x)"],
  ["Derivatives", "Trig derivatives", "d/dx sin(x) = cos(x),  d/dx cos(x) = -sin(x),  d/dx tan(x) = sec(x)^2", "diff(tan(x), x)"],
  ["Integrals", "Power rule", "integral x^n dx = x^(n + 1)/(n + 1) + C  (n != -1)", "integrate(x^4, x)"],
  ["Integrals", "Reciprocal", "integral 1/x dx = ln|x| + C", "integrate(1/x, x)"],
  ["Integrals", "Exponential", "integral e^(ax) dx = e^(ax)/a + C", "integrate(e^(2x), x)"],
  ["Integrals", "Sine and cosine", "integral sin(x) dx = -cos(x) + C,  integral cos(x) dx = sin(x) + C", "integrate(sin(x) + cos(x), x)"],
  ["Integrals", "Integration by parts", "integral u dv = u v - integral v du", "integrate(x e^x, x)"],
  ["Integrals", "Arctangent", "integral 1/(1 + x^2) dx = atan(x) + C", "integrate(1/(1 + x^2), x, 0, 1)"],
  ["Geometry", "Circle area", "A = pi r^2", "pi * 5^2"],
  ["Geometry", "Circumference", "C = 2 pi r", "2 * pi * 7"],
  ["Geometry", "Pythagoras", "a^2 + b^2 = c^2", "3^2 + 4^2 = c^2"],
  ["Geometry", "Triangle area", "A = b h / 2", "12 * 5 / 2"],
  ["Geometry", "Sphere volume", "V = 4/3 pi r^3", "4/3 * pi * 3^3"],
  ["Geometry", "Cylinder volume", "V = pi r^2 h", "pi * 2^2 * 10"],
  ["Geometry", "Cone volume", "V = pi r^2 h / 3", "pi * 3^2 * 4 / 3"],
  ["Geometry", "Distance between points", "d = sqrt((x2 - x1)^2 + (y2 - y1)^2)", "sqrt((7 - 1)^2 + (10 - 2)^2)"],
  ["Probability", "Combinations", "C(n, k) = n! / (k! (n - k)!)", "binomial(10, 3)"],
  ["Probability", "Permutations", "P(n, k) = n! / (n - k)!", "10! / 7!"],
  ["Probability", "Complement", "P(not A) = 1 - P(A)", "1 - (1/6)^3"],
  ["Probability", "Binomial probability", "P(X = k) = C(n, k) p^k (1 - p)^(n - k)", "binomial(5, 2) * (1/2)^2 * (1/2)^3"],
  ["Probability", "Expected value", "E[X] = sum x P(X = x)", "1*(1/6) + 2*(1/6) + 3*(1/6) + 4*(1/6) + 5*(1/6) + 6*(1/6)"],
  ["Probability", "Mean of data", "mean = (x_1 + ... + x_n) / n", "mean(4, 8, 15, 16, 23, 42)"],
  ["Probability", "Standard deviation", "s = sqrt(sum (x_i - mean)^2 / (n - 1))", "stdev(2, 4, 4, 4, 5, 5, 7, 9)"],
].map(([cat, name, formula, example]) => ({ cat, name, formula, example }));
export const FORMULA_CATEGORIES = [...new Set(FORMULAS.map((f) => f.cat))];
export function searchFormulas(q, cat = "") {
  const words = String(q || "").toLowerCase().split(/\s+/).filter(Boolean);
  return FORMULAS.filter((f) => (!cat || f.cat === cat) && words.every((w) => (f.cat + " " + f.name + " " + f.formula).toLowerCase().includes(w)));
}
