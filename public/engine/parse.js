// Quelvra parser: text / Unicode / LaTeX -> math tree.
//
//   parse(src)          -> node (throws QuelvraSyntaxError with .pos and .hint)
//   parseDetailed(src)  -> { node, warnings: [{ msg, pos }] }
//
// Pratt parser. Implicit multiplication (2x, 2(x+1), x y, sin x cos x) binds like explicit
// multiplication, left to right, so 1/2x is (1/2)x (a warning says so).

import * as N from "./num.js";
import * as X from "./expr.js";
import { toText } from "./print.js";

export class QuelvraSyntaxError extends Error {
  constructor(msg, pos, hint) {
    super(msg);
    this.name = "QuelvraSyntaxError";
    this.pos = pos;
    this.hint = hint || "";
  }
}

// ---------------- vocabulary ----------------
export const FUNCTIONS = new Set([
  "sin", "cos", "tan", "cot", "sec", "csc", "asin", "acos", "atan", "acot", "asec", "acsc",
  "sinh", "cosh", "tanh", "coth", "sech", "csch", "asinh", "acosh", "atanh",
  "ln", "log", "exp", "sqrt", "cbrt", "root", "abs", "sign", "floor", "ceil", "round",
  "gamma", "factorial", "gcd", "lcm", "mod", "max", "min", "binomial", "nCr", "nPr",
  "re", "im", "conj", "arg", "erf", "det", "inv", "transpose", "rank", "trace", "rref",
  "sum", "prod", "product", "diff", "derivative", "integrate", "integral", "limit",
  "solve", "simplify", "expand", "factor", "series", "taylor", "plot", "eigenvalues", "eigenvectors",
  "isprime", "factorint", "phi", "totient", "divisors", "mean", "median", "mode", "variance", "stdev",
  "Si", "Ci", "Shi", "Chi", "Ei", "li", "erfi", "erfc", "FresnelS", "FresnelC", "lambertw", "LambertW",
  "kaprekar", "collatz", "collatzverify", "goldbach", "goldbachverify", "twinprimes", "primegaps", "zetazeros", "eulerbricks", "movingsofa",
  // function analysis and geometry commands (call forms produced by the language engine)
  ...["domain", "range", "zeros", "intercepts", "asymptotes", "extrema", "inflection", "monotonic", "critical", "tangent", "normal", "inverse",
    "completesquare", "apart", "identity", "line", "slope", "distance", "midpoint", "arclength", "areabetween", "volume", "avgvalue",
    "maximize", "minimize", "dot", "cross", "piecewise"],
  // discrete math, probability and statistics (discrete.js, strategies/compute-more.js)
  ...["catalan", "fibonacci", "fib", "lucas", "subfactorial", "derangements", "multinomial", "stirling", "bell", "nthprime", "divisorsum", "numdivisors",
    "modinv", "powmod", "binompdf", "binomcdf", "geompdf", "geomcdf", "poissonpdf", "poissoncdf", "hypergeompdf", "normalpdf", "normalcdf",
    "invnorm", "pstdev", "pvariance", "quartiles", "iqr", "datarange", "zscore", "corr", "linreg", "tobase", "frombase",
    "polydiv", "polyrem", "polygcd", "coeff", "discriminant", "vertex", "wmean", "circle", "linedist", "rootsum", "rootprod", "diffat", "dblint", "grad", "solvein", "polar"],
]);
// Allowed argument counts; a call with any other count is a syntax error (never silently truncated).
const ARITY = new Map([
  ...["sin", "cos", "tan", "cot", "sec", "csc", "asin", "acos", "acot", "asec", "acsc", "sinh", "cosh", "tanh", "coth", "sech", "csch",
    "asinh", "acosh", "atanh", "ln", "exp", "sqrt", "cbrt", "abs", "sign", "floor", "ceil", "gamma", "factorial", "erf", "erfi", "erfc",
    "conj", "re", "im", "arg", "Si", "Ci", "Shi", "Chi", "Ei", "li", "FresnelS", "FresnelC", "isprime", "factorint", "phi", "divisors",
    "catalan", "fibonacci", "fib", "lucas", "subfactorial", "derangements", "bell", "nthprime", "divisorsum", "numdivisors"].map((n) => [n, [1]]),
  ...["binomial", "nCr", "nPr", "root", "stirling", "modinv", "geompdf", "geomcdf", "poissonpdf", "poissoncdf", "tobase", "frombase"].map((n) => [n, [2]]),
  ...["powmod", "binompdf", "binomcdf", "zscore"].map((n) => [n, [3]]),
  ["log", [1, 2]], ["round", [1, 2]], ["circle", [1]], ["linedist", [3]], ["rootsum", [1, 2]], ["rootprod", [1, 2]], ["diffat", [3]], ["dblint", [7]], ["solvein", [4, 6]], ["polar", [1]], ["hypergeompdf", [4]], ["normalpdf", [1, 3]], ["normalcdf", [2, 4]], ["invnorm", [1, 3]],
]);
const ALIASES = {
  arcsin: "asin", arccos: "acos", arctan: "atan", arccot: "acot", arcsec: "asec", arccsc: "acsc",
  arsinh: "asinh", arcosh: "acosh", artanh: "atanh", arcsinh: "asinh", arccosh: "acosh", arctanh: "atanh",
  lg: "log", tg: "tan", ctg: "cot", choose: "binomial", fact: "factorial", derivative: "diff",
  integral: "integrate", product: "prod", sd: "stdev", std: "stdev", totient: "phi",
};
const GREEK = [
  "alpha", "beta", "gamma", "delta", "epsilon", "varepsilon", "zeta", "eta", "theta", "vartheta", "iota", "kappa",
  "lambda", "mu", "nu", "xi", "omicron", "rho", "sigma", "tau", "upsilon", "phi", "varphi", "chi", "psi", "omega",
  "Gamma", "Delta", "Theta", "Lambda", "Xi", "Pi", "Sigma", "Phi", "Psi", "Omega",
];
const CONSTS = { pi: X.PI, e: X.E, i: X.I, oo: X.OO, inf: X.OO, infinity: X.OO, Infinity: X.OO, undefined: X.UNDEF };
const KEYWORDS = new Set(["lim", "int", "and", "or", "not", "d", "deg"]);
// special-function names are recognised only as a whole identifier ("li(x)", "Si(x)"), never
// found inside a longer run of letters, so "slip" is not s*li(p)
// Commands that are ordinary English words are call-form only: "domain(1/x, x)", never "domain of ...".
const CALL_ONLY = new Set(["domain", "range", "zeros", "intercepts", "asymptotes", "extrema", "inflection", "monotonic", "critical", "tangent", "normal", "inverse",
  "completesquare", "apart", "identity", "line", "slope", "distance", "midpoint", "arclength", "areabetween", "volume", "avgvalue",
  "maximize", "minimize", "dot", "cross", "piecewise", "bell", "vertex", "discriminant", "quartiles", "circle"]);
// The analysis commands are ordinary English words, so they are whole-identifier names too:
// "lineal" is never line*a*l, "normalise" never normal*i*s*e, "rangers" never range*r*s.
const WHOLE_ONLY = new Set(["li", "Si", "Ci", "Shi", "Chi", "Ei", "erfi", "erfc", "FresnelS", "FresnelC", "lambertw", "LambertW", "deg",
  "domain", "range", "zeros", "intercepts", "asymptotes", "extrema", "inflection", "monotonic", "critical", "tangent", "normal", "inverse",
  "completesquare", "apart", "identity", "line", "slope", "distance", "midpoint", "arclength", "areabetween", "volume", "avgvalue",
  "maximize", "minimize", "dot", "cross", "piecewise",
  "catalan", "fibonacci", "fib", "lucas", "subfactorial", "derangements", "multinomial", "stirling", "bell", "nthprime", "divisorsum", "numdivisors",
    "modinv", "powmod", "binompdf", "binomcdf", "geompdf", "geomcdf", "poissonpdf", "poissoncdf", "hypergeompdf", "normalpdf", "normalcdf",
    "invnorm", "pstdev", "pvariance", "quartiles", "iqr", "datarange", "zscore", "corr", "linreg", "tobase", "frombase",
    "polydiv", "polyrem", "polygcd", "coeff", "discriminant", "vertex", "wmean", "circle", "linedist", "rootsum", "rootprod", "diffat", "dblint", "grad", "solvein", "polar"]);
// ---- advanced continuous commands (engine/advanced/): bracket-only, whole-word names ----
import { ADVANCED_CONTINUOUS_COMMANDS, ADVANCED_CONTINUOUS_FUNCTIONS } from "./advanced/names.js";
for (const n of [...ADVANCED_CONTINUOUS_COMMANDS, ...ADVANCED_CONTINUOUS_FUNCTIONS]) { FUNCTIONS.add(n); CALL_ONLY.add(n); WHOLE_ONLY.add(n); }
// ---- end advanced continuous commands ----
// advanced discrete commands (engine/discrete/names.js; strategies/advanced-discrete.js): call-form
// names and argument helpers, recognised as whole identifiers only
import { ADV_DISCRETE_NAMES } from "./discrete/names.js";
for (const w of ADV_DISCRETE_NAMES) { FUNCTIONS.add(w); WHOLE_ONLY.add(w); }
const WORDS = [...FUNCTIONS, ...Object.keys(ALIASES), ...GREEK, ...Object.keys(CONSTS), ...KEYWORDS]
  .filter((w) => w.length > 1 && !WHOLE_ONLY.has(w))
  .sort((a, b) => b.length - a.length);

const UNI = {
  "×": "*", "·": "*", "∙": "*", "⋅": "*", "∗": "*", "÷": "/", "∕": "/",
  "−": "-", "–": "-", "—": "-", "≤": "<=", "≥": ">=", "≠": "!=", "≈": "~",
  "∞": " oo ", "π": " pi ", "→": "->", "⟶": "->", "∑": " sum", "Σ": " sum", "∏": " prod",
  "′": "'", "⁄": "/", "∗": "*",
  "α": " alpha ", "β": " beta ", "γ": " gamma ", "δ": " delta ", "ε": " epsilon ",
  "ζ": " zeta ", "η": " eta ", "θ": " theta ", "λ": " lambda ", "μ": " mu ", "ν": " nu ",
  "ξ": " xi ", "ρ": " rho ", "σ": " sigma ", "τ": " tau ", "φ": " phi ", "ϕ": " phi ",
  "χ": " chi ", "ψ": " psi ", "ω": " omega ", "Δ": " Delta ", "Ω": " Omega ",
  "ℂ": "C", "ℝ": "R", "∂": " d", "±": "+-", "⟨": "<", "⟩": ">", "〈": "<", "〉": ">", "⌊": " floor(", "⌋": ")", "⌈": " ceil(", "⌉": ")",
};
// vulgar fractions; after a digit they form a mixed number (2½ = 5/2)
const VULGAR = { "½": "1/2", "⅓": "1/3", "⅔": "2/3", "¼": "1/4", "¾": "3/4", "⅕": "1/5", "⅖": "2/5", "⅗": "3/5", "⅘": "4/5", "⅙": "1/6", "⅚": "5/6", "⅛": "1/8", "⅜": "3/8", "⅝": "5/8", "⅞": "7/8" };
const SUPERS = { "⁰": "0", "¹": "1", "²": "2", "³": "3", "⁴": "4", "⁵": "5", "⁶": "6", "⁷": "7", "⁸": "8", "⁹": "9", "⁻": "-", "⁺": "+", "ⁿ": "n", "ⁱ": "i", "ˣ": "x" };
const SUBS = { "₀": "0", "₁": "1", "₂": "2", "₃": "3", "₄": "4", "₅": "5", "₆": "6", "₇": "7", "₈": "8", "₉": "9" };

// ---------------- LaTeX -> text ----------------
function readGroup(s, i) {
  // s[i] must be "{" ; returns [content, nextIndex]
  let depth = 0, j = i;
  for (; j < s.length; j++) {
    if (s[j] === "{") depth++;
    else if (s[j] === "}") { depth--; if (depth === 0) return [s.slice(i + 1, j), j + 1]; }
  }
  throw new QuelvraSyntaxError("Unclosed { in LaTeX", i, "Add a matching }");
}
function readArg(s, i) {
  while (s[i] === " ") i++;
  if (s[i] === "{") return readGroup(s, i);
  if (s[i] === "\\") { const m = s.slice(i).match(/^\\[a-zA-Z]+/); return [m[0], i + m[0].length]; }
  return [s[i] || "", i + 1];
}
export function latexToText(src) {
  let s = src;
  if (!/\\|\{|\}/.test(s)) return s;
  s = s.replace(/\\left\s*\\?([|.])|\\right\s*\\?([|.])/g, (m, a, b) => ((a || b) === "|" ? "|" : " "));
  s = s.replace(/\^\s*\{?\s*\\circ\s*\}?|\\degree\b/g, "°");
  s = s.replace(/\\left|\\right|\\big|\\Big|\\bigg|\\Bigg|\\displaystyle|\\,|\\;|\\!|\\quad|\\qquad/g, " ");
  s = s.replace(/\\(mathrm|mathit|text|operatorname|mathbf)\{([^{}]*)\}/g, " $2 ");
  let out = "";
  for (let i = 0; i < s.length; ) {
    const c = s[i];
    if (c === "\\") {
      const m = s.slice(i).match(/^\\([a-zA-Z]+|.)/);
      const cmd = m[1];
      i += m[0].length;
      if (cmd === "frac" || cmd === "dfrac" || cmd === "tfrac") {
        const [a, j] = readArg(s, i);
        const [b, k] = readArg(s, j);
        const op = leibnizFrac(latexToText(a), latexToText(b));
        out += op || `((${latexToText(a)})/(${latexToText(b)}))`;
        i = k;
      } else if (cmd === "sqrt") {
        let idx = null;
        if (s[i] === "[") { const e = s.indexOf("]", i); idx = s.slice(i + 1, e); i = e + 1; }
        const [a, j] = readArg(s, i);
        out += idx ? ` root((${latexToText(a)}),(${latexToText(idx)}))` : ` sqrt(${latexToText(a)})`;
        i = j;
      } else if (cmd === "binom") {
        const [a, j] = readArg(s, i);
        const [b, k] = readArg(s, j);
        out += ` binomial((${latexToText(a)}),(${latexToText(b)}))`;
        i = k;
      } else if (cmd === "begin") {
        const [env, j] = readGroup(s, i);
        const end = s.indexOf("\\end{" + env + "}", j);
        const body = s.slice(j, end < 0 ? s.length : end);
        i = end < 0 ? s.length : end + 6 + env.length;
        if (/matrix|array/.test(env)) {
          const rows = body.replace(/\{[^}]*\}/, (x) => (env === "array" ? "" : x)).split(/\\\\/).map((r) => r.trim()).filter(Boolean);
          // cells are separated by & (whitespace only when a row has no &: "1 2 \\ 3 4")
          out += "[" + rows.map((r) => "[" + r.split(r.includes("&") ? /&/ : /\s+/).map((c) => c.trim()).filter(Boolean).map(latexToText).join(",") + "]").join(",") + "]";
        } else if (env === "cases") {
          // rows "value & condition"; "if"/"for" words are dropped, an "otherwise" row is the default
          out += " piecewise(" + body.split(/\\\\/).filter((r) => r.trim()).map((r) => {
            const [v, c = ""] = r.split("&");
            const cond = c.replace(/\\text\{([^{}]*)\}/g, " $1 ").replace(/^\s*,?\s*(?:if|for|when)\b/i, "").trim();
            return /^(?:otherwise|else|elsewhere)?$/i.test(cond) ? latexToText(v) : latexToText(v) + "," + latexToText(cond);
          }).join(",") + ")";
        } else out += latexToText(body);
      } else if (cmd === "cdot" || cmd === "times" || cmd === "ast") out += "*";
      else if (cmd === "div") out += "/";
      else if (cmd === "le" || cmd === "leq" || cmd === "leqslant") out += "<=";
      else if (cmd === "equiv") out += "≡";
      else if (cmd === "pmod") { const [a, j] = readArg(s, i); out += ` (mod ${latexToText(a)})`; i = j; }
      else if (cmd === "bmod" || cmd === "mod") out += " mod ";
      else if (cmd === "lfloor") out += " floor(";
      else if (cmd === "lceil") out += " ceil(";
      else if (cmd === "rfloor" || cmd === "rceil") out += ")";
      else if (cmd === "mp") out += "∓";
      else if (cmd === "langle") out += "<";
      else if (cmd === "rangle") out += ">";
      else if (cmd === "ge" || cmd === "geq" || cmd === "geqslant") out += ">=";
      else if (cmd === "ne" || cmd === "neq") out += "!=";
      else if (cmd === "to" || cmd === "rightarrow") out += "->";
      else if (cmd === "infty") out += " oo ";
      else if (cmd === "int") out += " int";
      else if (cmd === "sum") out += " sum";
      else if (cmd === "prod") out += " prod";
      else if (cmd === "lim") out += " lim";
      else if (cmd === "pm") out += "+-";
      else if (cmd === "circ" || cmd === "degree") out += "deg";
      else if (cmd === "partial") out += " d";
      else if (cmd === "{" || cmd === "}") out += cmd === "{" ? "{" : "}";
      else if (cmd === "|" ) out += "|";
      else if (cmd === "lvert" || cmd === "rvert" || cmd === "vert" || cmd === "mid") out += "|";
      else if (cmd === "cdots" || cmd === "ldots" || cmd === "dots") out += "...";
      // a function name keeps its sub/superscript attached: \log_{2} 8 -> log_{2} 8
      else out += " " + cmd + (s[i] === "_" || s[i] === "^" ? "" : " ");
    } else if (c === "{") {
      const [a, j] = readGroup(s, i);
      // {1, 2, 3} not attached to ^ or _ is a set literal; other brace groups are grouping
      const prev = out.replace(/\s+$/, "").slice(-1);
      let depth = 0, comma = false;
      for (const ch of a) { if ("([{".includes(ch)) depth++; else if (")]}".includes(ch)) depth--; else if (ch === "," && depth === 0) comma = true; }
      if (prev === "_" && /^[A-Za-z0-9]+$/.test(a.trim())) out += "{" + a.trim() + "}";
      else if (prev !== "^" && prev !== "_" && /^\s*[A-Za-z]\w*\s*(?:\||:|\\mid\b)/.test(a)) out += "{" + latexToText(a) + "}"; // set-builder
      else if (comma && prev !== "^" && prev !== "_") out += "{" + latexToText(a) + "}";
      else out += "(" + latexToText(a) + ")";
      i = j;
    } else {
      out += c === "&" ? " " : c;
      i++;
    }
  }
  return out;
}

// \frac{d}{dx}, \frac{dy}{dx}, \frac{d^2 y}{dx^2}, \frac{\partial}{\partial x}: Leibniz operators, not fractions
function leibnizFrac(a, b) {
  const A = a.replace(/\s+/g, ""), B = b.replace(/\s+/g, "");
  const ma = A.match(/^d(?:\^\(?(\d+)\)?)?([A-Za-z])?$/), mb = B.match(/^d([A-Za-z])(?:\^\(?(\d+)\)?)?$/);
  if (!ma || !mb) return null;
  const n = ma[1] || "1";
  if ((mb[2] || "1") !== n) return null;
  return n === "1" ? ` d${ma[2] || ""}/d${mb[1]} ` : ` d^${n}${ma[2] || ""}/d${mb[1]}^${n} `;
}

// ---------------- lexer ----------------
// Text-level normalisation. Readings that a person could mean two ways are recorded in `notes`
// (they become parse warnings, which the UI shows): mixed numbers, thousands separators and the
// "3.2 x 10^5" times sign.
function normalise(src, notes = []) {
  let s = latexToText(String(src));
  // vulgar fractions: 2½ is the mixed number 5/2, a lone ½ is 1/2
  s = s.replace(/(\d+)\s*([½⅓⅔¼¾⅕⅖⅗⅘⅙⅚⅛⅜⅝⅞])/g, (m, a, f) => `(${a}+${VULGAR[f]})`).replace(/[½⅓⅔¼¾⅕⅖⅗⅘⅙⅚⅛⅜⅝⅞]/g, (f) => `(${VULGAR[f]})`);
  // superscripts: x² -> x^(2)
  s = s.replace(/[⁰¹²³⁴-⁹⁻⁺ⁿⁱˣ]+/g, (m) => "^(" + [...m].map((c) => SUPERS[c]).join("") + ")");
  // subscripts as a braced group, so a digit after them stays separate: log₂8 -> log_{2} 8
  s = s.replace(/[₀-₉]+/g, (m) => "_{" + [...m].map((c) => SUBS[c]).join("") + "} ");
  s = s.replace(/[^\x00-\x7f]/g, (c) => (c === "√" || c === "∛" || c === "∜" || c === "∫" || c === "°" || c === "≡" || c === "∓" ? c : UNI[c] ?? c));
  s = s.replace(/\*\*/g, "^");
  // scientific notation written with a letter x: 3.2 x 10^-5, 3.2x10^5 (never the variable x here)
  s = s.replace(/(\d)\s*[xX]\s*(10\s*\^)/g, (m, a, b) => { notes.push(`Read "${m.replace(/\s*\^$/, "")}" as scientific notation (x means times).`); return `${a}*${b}`; });
  // mixed numbers: 2 1/2 = 5/2 (a whole number, a space, then a proper fraction)
  s = s.replace(/(?<![\w.)\]}^\/*!'|]\s*)(\d+) +(\d+)\/(\d+)(?![\w.(^\/!|]|\s*[\^(])/g, (m, a, n, d) => {
    if (!(BigInt(n) > 0n && BigInt(n) < BigInt(d))) return m;
    notes.push(`Read "${m}" as the mixed number ${a} + ${n}/${d}. Write ${a}*${n}/${d} for a product.`);
    return `(${a}+${n}/${d})`;
  });
  // thousands separators at the top level only: 1,000,000 -> 1000000 (inside brackets a comma separates arguments)
  s = s.replace(/(?<![\w.,])([1-9]\d{0,2}(?:,\d{3})+)(\.\d+)?(?![\d])(?!,\d)/g, (m, a, b, off, str) => {
    let depth = 0;
    for (let k = 0; k < off; k++) { const ch = str[k]; if ("([{<".includes(ch)) depth++; else if (")]}>".includes(ch)) depth--; }
    if (depth !== 0) return m;
    notes.push(`Read "${m}" as ${a.replace(/,/g, "")}${b || ""} (commas as thousands separators).`);
    return a.replace(/,/g, "") + (b || "");
  });
  return s;
}

// names that take glued digits as their argument (sin2x = sin(2x), ln2 = ln(2)); log keeps the
// base reading (log2(8) = log_2(8)); Greek letters keep the subscript reading (theta2 = theta_2,
// like x2 = x_2, the usual way to name a second variable)
const GLUE_ARG = (n) => FUNCTIONS.has(n) && !GREEK.includes(n) && !["log", "re", "im", "li", "Si", "Ci", "Ei", "mod"].includes(n);

function lex(s, notes = []) {
  const toks = [];
  let i = 0;
  const push = (t, v, start) => toks.push({ t, v, s: start, e: i });
  while (i < s.length) {
    const c = s[i];
    const start = i;
    if (/\s/.test(c)) { i++; continue; }
    if (/[0-9]/.test(c) || (c === "." && /[0-9]/.test(s[i + 1] || ""))) {
      let m = s.slice(i).match(/^(\d+\.?\d*|\.\d+)([eE][+-]?\d+)?/);
      // "2e" followed by non-digit is 2*e, not scientific
      i += m[0].length;
      push("num", m[0], start);
      continue;
    }
    if (/[A-Za-z]/.test(c)) {
      let m = s.slice(i).match(/^[A-Za-z]+(_\{?[A-Za-z0-9]+\}?|_?[0-9]+)?/);
      // big operators take their subscript as a bound, not as part of the name
      const word = m[0].match(/^[A-Za-z]+/)[0];
      if (["int", "sum", "prod", "lim"].includes(word) && m[0] !== word) m = [word];
      if (m[1] && /^[0-9]/.test(m[1])) {
        const parts = splitIdent(word), last = parts[parts.length - 1];
        const fname = ALIASES[last] || last;
        if (GLUE_ARG(fname)) {
          if (s[i + m[0].length] === "(") throw new QuelvraSyntaxError(`"${m[0]}(" is ambiguous`, start, `Write ${last}(${m[1]}...) for the argument ${m[1]}..., or ${last}^${m[1]}(...) for a power`);
          m = [word];
        } else if (fname === "log" && /^[A-Za-z]/.test(s[i + m[0].length] || "")) {
          notes.push(`Read "${m[0]}${s.slice(i + m[0].length).match(/^[A-Za-z]+/)[0]}" as log base ${m[1]}; write log(${m[1]}x) for the logarithm of ${m[1]}x.`);
        }
      }
      // compound subscript: a_(n+1), x_{2k}, T_(i-1) -> one indexed symbol a_{n+1}
      const after = i + m[0].length;
      if (m[0] === word && !["int", "sum", "prod", "lim", "log"].includes(word) && s[after] === "_" && (s[after + 1] === "(" || s[after + 1] === "{")) {
        const close = s[after + 1] === "(" ? ")" : "}";
        const end = s.indexOf(close, after + 2);
        const inner = end > 0 ? s.slice(after + 2, end).replace(/\s+/g, "") : "";
        if (inner && /^[A-Za-z0-9+\-*]+$/.test(inner) && !/[(){}]/.test(s.slice(after + 2, end))) {
          i = end + 1;
          push("id", /^[A-Za-z0-9]+$/.test(inner) ? `${word}_${inner}` : `${word}_{${inner}}`, start);
          continue;
        }
      }
      i += m[0].length;
      push("id", m[0], start);
      continue;
    }
    const two = s.slice(i, i + 2);
    if (["<=", ">=", "!=", "->", "==", "+-", "=>", "<>", ":="].includes(two)) {
      i += 2;
      push("op", two === "==" ? "=" : two === "<>" ? "!=" : two === "=>" ? ">=" : two === ":=" ? "=" : two, start);
      continue;
    }
    if (s.slice(i, i + 3) === "...") { i += 3; push("op", "...", start); continue; }
    i++;
    if ("+-*/^=<>!,;:|()[]{}_'%~".includes(c) || c === "√" || c === "∛" || c === "∜" || c === "∫" || c === "°" || c === "≡" || c === "∓") {
      push("op", c === "∫" ? "int" : c, start);
      continue;
    }
    throw new QuelvraSyntaxError(`Unexpected character "${c}"`, start, "Remove it or replace it with a math symbol");
  }
  toks.push({ t: "eof", v: "", s: i, e: i });
  return toks;
}

// Split an identifier run into known words / single letters: "sinx" -> sin, x ; "xy" -> x, y
function splitIdent(raw) {
  const m = raw.match(/^([A-Za-z]+)(_\{?([A-Za-z0-9+\-*]+)\}?|_?([0-9]+))?$/);
  const letters = m[1];
  const subscript = m[3] || m[4] || "";
  if (FUNCTIONS.has(letters) || ALIASES[letters] || GREEK.includes(letters) || CONSTS[letters] || KEYWORDS.has(letters)) {
    return [subscript ? letters + "_" + subscript : letters];
  }
  const out = [];
  let i = 0;
  while (i < letters.length) {
    const rest = letters.slice(i);
    const w = WORDS.find((w) => rest.startsWith(w));
    if (w) { out.push(w); i += w.length; }
    else { out.push(letters[i]); i++; }
  }
  if (subscript) out[out.length - 1] += "_" + subscript;
  return out;
}

// ---------------- parser ----------------
const BP = { rel: 10, or: 4, and: 6, add: 20, mul: 30, neg: 35, pow: 40, post: 50 };
const RELS = new Set(["=", "<", ">", "<=", ">=", "!=", "~", "≡"]);

class Parser {
  constructor(src) {
    this.src = src;
    const notes = [];
    const raw = lex(normalise(src, notes), notes);
    // expand identifier runs
    this.toks = [];
    for (const t of raw) {
      if (t.t === "id") {
        const parts = splitIdent(t.v);
        for (const p of parts) this.toks.push({ t: "id", v: p, s: t.s, e: t.e, raw: t.v });
      } else this.toks.push(t);
    }
    this.i = 0;
    this.warnings = notes.map((msg) => ({ msg, pos: 0 }));
    this.lastInfixMod = null;
    this.diffStop = 0; // > 0 while parsing an integrand: stop at "d<var>"
    this.barDepth = 0;
    this.userFns = new Set(["f", "g", "h"]);
    this.bound = [];
  }
  peek(k = 0) { return this.toks[this.i + k]; }
  next() { return this.toks[this.i++]; }
  at(v) { const t = this.peek(); return t.t === "op" && t.v === v; }
  eat(v) { if (this.at(v)) { this.i++; return true; } return false; }
  expect(v, hint) {
    if (!this.eat(v)) {
      const t = this.peek();
      throw new QuelvraSyntaxError(`Expected "${v}"${t.t === "eof" ? " at end of input" : ` before "${t.v}"`}`, t.s, hint || `Insert "${v}"`);
    }
  }
  err(msg, t = this.peek(), hint) { throw new QuelvraSyntaxError(msg, t.s, hint); }

  // Is token t a differential "dx" in an integrand?
  isDiff(k = 0) {
    const t = this.peek(k);
    if (t.t !== "id" || t.v !== "d") return false;
    const n = this.peek(k + 1);
    if (n.t !== "id" || FUNCTIONS.has(n.v) || n.v === "d") return false;
    if (n.s === t.s) return true; // "dx" written as one word
    return this.diffStop > 0 && !this.startsPrimary(this.peek(k + 2));
  }

  parseTop() {
    const items = [this.parseExpr(0)];
    while (this.eat(",") || this.eat(";")) {
      if (this.peek().t === "eof") break;
      items.push(this.parseExpr(0));
    }
    if (this.peek().t !== "eof") {
      const t = this.peek();
      if (t.v === ")" || t.v === "]") this.err(`Unmatched "${t.v}"`, t, `Remove "${t.v}" or add the opening bracket`);
      this.err(`Unexpected "${t.v}"`, t);
    }
    if (items.length === 1) return items[0];
    if (items.every((u) => X.isRelation(u) || u.k === "and")) return X.system(...items);
    return X.tuple(...items);
  }

  parseExpr(rbp) {
    let left = this.nud(this.next());
    for (;;) {
      const t = this.peek();
      if (t.t === "eof") break;
      if (this.diffStop && this.isDiff()) break;
      const lbp = this.lbp(t);
      if (lbp <= rbp) break;
      left = this.led(this.next(), left);
    }
    return left;
  }

  startsPrimary(t) {
    if (t.t === "num" || t.t === "id") return !(t.t === "id" && (t.v === "and" || t.v === "or"));
    return t.t === "op" && ["(", "√", "∛", "∜", "int", "["].includes(t.v);
  }

  lbp(t) {
    if (t.t === "op") {
      if (RELS.has(t.v)) return BP.rel;
      if (t.v === "+" || t.v === "-" || t.v === "+-" || t.v === "∓") return BP.add;
      // "3x = 2 (mod 7)": the bracketed modulus belongs to the congruence, it is not a factor
      if (t.v === "(" && this.peek(1).t === "id" && this.peek(1).v === "mod") return 0;
      if (t.v === "*" || t.v === "/") return BP.mul;
      if (t.v === "^") return BP.pow;
      if (t.v === "!" || t.v === "%" || t.v === "°" || t.v === "'") return BP.post;
      if (t.v === "|") return this.barDepth > 0 ? 0 : BP.mul; // 2|x| is 2*|x|
      if (this.startsPrimary(t)) return BP.mul; // implicit multiplication: 2(x+1), 2sqrt(x)
      return 0;
    }
    if (t.t === "id" && (t.v === "and" || t.v === "or")) return t.v === "and" ? BP.and : BP.or;
    if (t.t === "id" && t.v === "mod") return BP.mul;
    if (t.t === "id" && t.v === "deg") return BP.post;
    if (this.startsPrimary(t)) return BP.mul; // implicit multiplication
    return 0;
  }

  led(t, left) {
    if (t.t === "op") {
      switch (t.v) {
        case "+": return X.add(left, this.parseExpr(BP.add));
        case "-": return X.sub(left, this.parseExpr(BP.add));
        case "+-": return X.fn("pm", left, this.parseExpr(BP.add));
        case "∓": return X.fn("pm", left, X.neg(this.parseExpr(BP.add)));
        case "*": return X.mul(left, this.parseExpr(BP.mul));
        case "/": {
          const right = this.parseExpr(BP.mul);
          // warn on 1/2x style
          const nt = this.peek();
          void nt;
          return X.div(left, right);
        }
        case "^": {
          const right = this.parseExpr(BP.pow - 1);
          return X.pow(left, right);
        }
        case "!":
          if (this.eat("!")) return X.fn("factorial2", left);
          return X.fn("factorial", left);
        case "%": return X.mul(left, X.num(1, 100));
        case "°": return X.mul(left, X.div(X.PI, X.num(180)));
        case "'": {
          // f'(x) -> derivative of f(x)
          return X.fn("prime", left);
        }
        default:
          if (RELS.has(t.v)) {
            const right = this.parseExpr(BP.rel);
            if (t.v === "=" || t.v === "≡") {
              const cg = this.congruenceTail(t, left, right);
              if (cg) return cg;
            }
            const node = t.v === "=" ? X.eq(left, right) : t.v === "~" ? X.fn("approx", left, right) : X.rel(t.v, left, right);
            // chained: a < b < c
            if (RELS.has(this.peek().v) && this.peek().t === "op" && t.v !== "=") {
              const t2 = this.next();
              const r2 = this.parseExpr(BP.rel);
              return X.and(node, X.rel(t2.v, right, r2));
            }
            return node;
          }
          // implicit multiplication with a bracket / radical / integral
          this.i--;
          return this.implicit(left);
      }
    }
    if (t.t === "id" && (t.v === "and" || t.v === "or")) {
      const right = this.parseExpr(t.v === "and" ? BP.and : BP.or);
      return t.v === "and" ? X.and(left, right) : X.or(left, right);
    }
    if (t.t === "id" && t.v === "mod") {
      const node = X.fn("mod", left, this.parseExpr(BP.mul));
      this.lastInfixMod = { node, end: this.i };
      return node;
    }
    if (t.t === "id" && t.v === "deg") return X.mul(left, X.div(X.PI, X.num(180)));
    this.i--;
    return this.implicit(left);
  }

  // Congruences: a ≡ b (mod m), a ≡ b mod m, a = b (mod m), and a = b mod m. The integer solver
  // (solve/integer.js) reads them as mod(A, m) = r with 0 <= r < m. "y = x mod 5" (a lone symbol
  // equal to a remainder of other variables) stays the remainder function.
  congruenceTail(t, left, right) {
    let m = null, r = right, infix = false;
    if (this.at("(") && this.peek(1).t === "id" && this.peek(1).v === "mod") {
      this.next(); this.next();
      m = this.parseExpr(0);
      this.expect(")", "Close the modulus with )");
    } else if (this.lastInfixMod && this.lastInfixMod.node === right && this.lastInfixMod.end === this.i) {
      m = right.args[1]; r = right.args[0]; infix = true;
    }
    if (!m) {
      if (t.v === "≡") this.err("A congruence needs a modulus", this.peek(), "Write it as 3x ≡ 2 (mod 7)");
      return null;
    }
    if (infix && t.v === "=" && left.k === "sym" && X.freeSymbols(r).size && X.freeOf(r, left)) return null;
    if (!X.isInt(m) || m.v.n <= 0n) this.err("The modulus of a congruence must be a positive whole number", t, "Write it as 3x ≡ 2 (mod 7)");
    const M = m.v.n;
    const red = (u) => X.num(((u.v.n % M) + M) % M);
    let node;
    if (X.isInt(r)) node = X.eq(X.fn("mod", left, m), red(r));
    else if (X.isInt(left)) node = X.eq(X.fn("mod", r, m), red(left));
    else node = X.eq(X.fn("mod", X.sub(left, r), m), X.ZERO);
    if (infix && t.v === "=") this.warnings.push({ msg: `Read "... = ... mod ${M}" as a congruence modulo ${M}. Write mod(a, ${M}) for the remainder itself.`, pos: t.s });
    this.congruence = true; // congruence notation means the unknowns are integers
    return node;
  }

  // Leibniz notation after a "d": dy/dx, d^2y/dx^2 (also df/dx, and ∂f/∂x which arrives as df/dx).
  // Only when "dy" and "dx" are each written as one word, so d*y/(d*x) with spaces is not reinterpreted.
  leibniz(t) {
    const save = this.i;
    let order = X.ONE;
    const oneWord = (a, b) => a.t === "id" && b.t === "id" && a.s === b.s;
    if (this.at("^")) {
      this.next();
      const o = this.next();
      if (o.t !== "num" || !/^\d+$/.test(o.v)) { this.i = save; return null; }
      order = X.num(BigInt(o.v));
    }
    const y = this.peek(), sl = this.peek(1), d2 = this.peek(2), x = this.peek(3);
    const ok = y.t === "id" && y.v.length >= 1 && !FUNCTIONS.has(y.v) && y.v !== "d" && !CONSTS[y.v] && (order === X.ONE ? oneWord(t, y) : true) &&
      sl.t === "op" && sl.v === "/" && d2.t === "id" && d2.v === "d" && oneWord(d2, x) && x.t === "id" && !FUNCTIONS.has(x.v) && !CONSTS[x.v];
    if (!ok) { this.i = save; return null; }
    this.i += 4;
    if (order !== X.ONE) {
      if (!this.eat("^")) { this.i = save; return null; }
      const o2 = this.next();
      if (o2.t !== "num" || X.num(BigInt(o2.v)) !== order) { this.i = save; return null; }
    }
    return X.deriv(X.sym(y.v), X.sym(x.v), order);
  }

  implicit(left) {
    const right = this.parseExpr(BP.mul);
    if (left.k === "mul" && left.args.length === 2 && left.args[1].k === "pow" && left.args[1].args[1] === X.NEG_ONE && X.isNum(left.args[0]) && X.isNum(left.args[1].args[0])) {
      this.warnings.push({ msg: "Read a/b c as (a/b)c. Use parentheses for a/(bc).", pos: this.peek().s });
    }
    return X.mul(left, right);
  }

  // argument of a function written without parentheses: sin 2x, sin x^2, ln x
  fnArgNoParen() {
    let arg = this.parseExpr(BP.neg);
    for (;;) {
      const t = this.peek();
      if (t.t === "eof" || !this.startsPrimary(t)) break;
      if (t.t === "id" && (FUNCTIONS.has(t.v) || ALIASES[t.v] || t.v === "lim" || t.v === "int" || t.v === "d")) break;
      if (t.t === "op" && t.v !== "(" && t.v !== "√") break;
      if (t.t === "op" && t.v === "(") break; // sin x (x+1): stop, multiply outside
      if (this.diffStop && this.isDiff()) break;
      arg = X.mul(arg, this.parseExpr(BP.neg));
    }
    return arg;
  }

  parseArgs() {
    this.expect("(");
    const args = [];
    if (!this.at(")")) {
      do { args.push(this.parseExpr(0)); } while (this.eat(","));
    }
    this.expect(")", "Close the function call with )");
    return args;
  }

  nud(t) {
    if (t.t === "eof") this.err("Expression ended too early", t, "Finish the expression");
    if (t.t === "num") {
      const v = N.fromDecimal(t.v);
      return X.num(v);
    }
    if (t.t === "op") {
      switch (t.v) {
        case "(": {
          if (this.at(")")) this.err("Empty parentheses", t);
          const save = this.diffStop;
          this.diffStop = 0;
          const e = this.parseExpr(0);
          if (this.eat(",")) {
            const items = [e];
            do { items.push(this.parseExpr(0)); } while (this.eat(","));
            this.diffStop = save;
            // (a, b] is a half-open interval; (a, b) stays a pair (a point or an open interval)
            if (items.length === 2 && this.eat("]")) return X.interval(items[0], items[1], true, false);
            this.expect(")");
            return X.tuple(...items);
          }
          this.diffStop = save;
          this.expect(")", "Add the missing closing parenthesis");
          return e;
        }
        case "[": {
          const save = this.diffStop;
          this.diffStop = 0;
          const rows = [[]];
          if (!this.at("]")) {
            rows[0].push(this.parseExpr(0));
            for (;;) {
              if (this.eat(",")) rows[rows.length - 1].push(this.parseExpr(0));
              else if (this.eat(";")) rows.push([this.parseExpr(0)]);
              else break;
            }
          }
          this.diffStop = save;
          // [a, b) is a half-open interval; [a, b] stays a list (read as a vector)
          if (rows.length === 1 && rows[0].length === 2 && this.eat(")")) return X.interval(rows[0][0], rows[0][1], false, true);
          this.expect("]");
          if (rows.length > 1) return X.matrix(rows.map((r) => X.tuple(...r)));
          const items = rows[0];
          if (items.length && items.every((u) => u.k === "vector")) {
            const w = items[0].args.length;
            if (items.every((u) => u.args.length === w)) return X.matrix(items.map((u) => X.tuple(...u.args)));
          }
          return X.vector(...items);
        }
        case "{": {
          // set-builder {x | x > 0}, {x : x^2 < 4}: the set of x satisfying the condition
          if (this.peek().t === "id" && this.peek(1).t === "op" && (this.peek(1).v === "|" || this.peek(1).v === ":")) {
            const v = this.next();
            this.next();
            const cond = this.parseExpr(0);
            this.expect("}");
            if (!X.isRelation(cond) && cond.k !== "and" && cond.k !== "or") this.err("A set-builder condition must be a relation, like {x | x > 0}", v);
            this.warnings.push({ msg: `Read {${v.v} | ...} as the set of ${v.v} satisfying the condition; Quelvra solves the condition for ${v.v}.`, pos: t.s });
            return cond;
          }
          const items = [];
          if (!this.at("}")) do { items.push(this.parseExpr(0)); } while (this.eat(","));
          this.expect("}");
          return X.set(...items);
        }
        case "-": {
          const e = this.parseExpr(BP.neg);
          if (X.isNum(e)) return X.num(N.neg(e.v));
          return X.neg(e);
        }
        case "+": return this.parseExpr(BP.neg);
        case "<": {
          // angle-bracket vector <1, 2, 3>
          const items = [this.parseExpr(BP.rel)];
          while (this.eat(",")) items.push(this.parseExpr(BP.rel));
          this.expect(">", "Close the vector with >");
          return X.vector(...items);
        }
        case "|": {
          this.barDepth++;
          const save = this.diffStop;
          this.diffStop = 0;
          const e = this.parseExpr(0);
          this.diffStop = save;
          this.barDepth--;
          this.expect("|", "Close the absolute value with |");
          return X.fn("abs", e);
        }
        case "√": return X.sqrt(this.parseExpr(BP.pow - 1));
        case "∛": return X.pow(this.parseExpr(BP.pow - 1), X.num(1, 3));
        case "∜": return X.pow(this.parseExpr(BP.pow - 1), X.num(1, 4));
        case "int": return this.parseIntegral(t);
        default:
          this.err(`Unexpected "${t.v}"`, t, t.v === ")" ? "Remove the extra )" : "");
      }
    }
    // identifiers
    let name = t.v;
    if (ALIASES[name]) name = ALIASES[name];
    if (name === "lim") return this.parseLimit(t);
    if (name === "int" && !this.at("(")) return this.parseIntegral(t);
    if (name === "int") name = "integrate";
    if ((name === "sum" || name === "prod") && (this.at("_") || !this.at("("))) return this.parseBigOp(name, t);
    if (name === "d" && !this.at("/")) {
      const lz = this.leibniz(t);
      if (lz) return lz;
    }
    // d/dx
    if (name === "d" && this.at("/") ) {
      const n1 = this.peek(1);
      if (n1.t === "id" && n1.v === "d") {
        const n2 = this.peek(2);
        if (n2.t === "id") {
          this.i += 3;
          const v = X.sym(n2.v);
          const body = this.at("(") ? this.parseExpr(BP.add) : this.parseExpr(BP.add);
          return X.deriv(body, v, X.ONE);
        }
      }
    }
    if (name === "d" && this.at("^")) {
      // d^2/dx^2 f
      const save = this.i;
      this.next();
      const ord = this.next();
      if (ord.t === "num" && this.eat("/")) {
        const d2 = this.next(), v = this.next();
        if (d2.v === "d" && v.t === "id") {
          this.eat("^");
          const o2 = this.peek();
          if (o2.t === "num") this.next();
          const body = this.parseExpr(BP.add);
          return X.deriv(body, X.sym(v.v), X.num(N.fromDecimal(ord.v)));
        }
      }
      this.i = save;
    }
    const lb = name.match(/^log_(.+)$/);
    if (lb) return this.parseFunction("log", t, /^\d+$/.test(lb[1]) ? X.num(BigInt(lb[1])) : lb[1] === "e" ? X.E : X.sym(lb[1]));
    if (FUNCTIONS.has(name)) return this.parseFunction(name, t);
    if (CONSTS[name] && !this.bound.includes(name)) return CONSTS[name];
    // user function call f(x), or implicit product x(x+1)
    if (this.at("(") && this.userFns.has(name)) {
      const args = this.parseArgs();
      return X.fn(name, ...args);
    }
    if (this.at("'") && this.userFns.has(name)) {
      let order = 0;
      while (this.eat("'")) order++;
      const args = this.parseArgs();
      return X.deriv(X.fn(name, ...args), args[0], X.num(order));
    }
    return X.sym(name);
  }

  parseFunction(name, t, presetBase = null) {
    // power on the function name: sin^2 x, sin^-1 x
    let power = null;
    if (this.at("^")) {
      this.next();
      power = this.at("(") ? this.parseExpr(BP.pow) : this.parseExpr(BP.pow);
      if (X.isNum(power) && power.v.n === -1n && power.v.d === 1n && ["sin", "cos", "tan", "cot", "sec", "csc", "sinh", "cosh", "tanh"].includes(name)) {
        name = "a" + name;
        power = null;
      }
    }
    // log base: log_2(x), log_{10} x, log_b x
    let base = presetBase;
    if (name === "log" && !base && this.at("_")) {
      this.next();
      base = this.braceGroup() || this.parseExpr(BP.post);
    }
    const tk = this.peek();
    let m = null;
    if (tk.t === "id") {
      // identifier with subscript glued, e.g. "log_2" lexed as id "log_2"
    }
    let args;
    if (this.at("(")) args = this.parseArgs();
    else if (CALL_ONLY.has(name)) this.err(`"${name}" is used as a command with brackets`, t, `Write ${name}(...), for example ${name === "piecewise" ? "piecewise(x, x > 0, -x, x <= 0)" : name + "(1/x, x)"}`);
    else {
      if (this.peek().t === "eof" || (!this.startsPrimary(this.peek()) && !this.at("-") && !this.at("|"))) this.err(`"${name}" needs an argument`, this.peek(), `Write ${name}(x)`);
      if (this.at("|")) args = [this.nud(this.next())];
      else if (this.at("-")) { this.next(); args = [X.neg(this.fnArgNoParen())]; }
      else args = [this.fnArgNoParen()];
    }
    void m;
    const ar = ARITY.get(name);
    if (ar && !ar.includes(args.length)) this.err(`${name} takes ${ar.join(" or ")} argument${ar.length === 1 && ar[0] === 1 ? "" : "s"}, not ${args.length}`, t, `Write ${name}(${Array.from({ length: ar[0] }, (_, i) => "abcd"[i]).join(", ")})`);
    let node;
    if (name === "log") {
      if (base) node = X.fn("log", base, args[0]);
      else if (args.length === 2) node = X.fn("log", args[0], args[1]);
      else node = X.fn("log", X.num(10), args[0]);
    } else if (name === "sqrt") node = X.sqrt(args[0]);
    else if (name === "cbrt") node = X.pow(args[0], X.num(1, 3));
    else if (name === "exp") node = X.exp(args[0]);
    else if (name === "root") node = X.pow(args[0], X.recip(args[1]));
    else if (name === "piecewise") {
      // piecewise(value1, condition1, value2, condition2, ..., [default])
      if (args.length < 2) this.err("piecewise needs value, condition pairs", t, "Write piecewise(x, x > 0, -x, x <= 0)");
      node = X.piecewise(...args, ...(args.length % 2 ? [X.TRUE] : []));
    }
    else if (name === "diff") {
      const [e, v = this.guessVar(e), ord = X.ONE] = args;
      node = X.deriv(e, v, ord);
    } else if (name === "integrate") {
      const [e, v = this.guessVar(e), lo, hi] = args;
      node = lo === undefined ? X.integral(e, v) : X.integral(e, v, lo, hi);
    } else if (name === "limit") {
      const [e, v, to, dir] = args;
      const d = dir && dir.k === "sym" ? (dir.name === "plus" ? "+" : dir.name === "minus" ? "-" : "") : dir && X.isNum(dir) ? (dir.v.n > 0n ? "+" : "-") : "";
      node = X.limit(e, v, to, d);
    } else if (name === "sum" || name === "prod") {
      const [e, v, lo, hi] = args;
      node = name === "sum" ? X.sum(e, v, lo, hi) : X.product(e, v, lo, hi);
    } else node = X.fn(name, ...args);
    if (power) node = X.pow(node, power);
    return node;
  }

  guessVar(e) {
    const fs = [...X.freeSymbols(e)];
    return X.sym(fs.includes("x") ? "x" : fs.sort()[0] || "x");
  }

  // an integral/sum bound written without brackets: an optional sign then one atom, so
  // int_-1^1 reads lo = -1, hi = 1 (not lo = (-1)^1) and int_-oo^oo reads -oo .. oo
  // a LaTeX brace group {..} used as a bound or a log base (not a set)
  braceGroup() {
    if (!this.at("{")) return null;
    this.next();
    const save = this.diffStop;
    this.diffStop = 0;
    const e = this.parseExpr(0);
    this.diffStop = save;
    this.expect("}");
    return e;
  }

  parseBound() {
    const g = this.braceGroup();
    if (g) return g;
    if (this.at("-") || this.at("+")) {
      const neg = this.next().v === "-";
      const a = this.parseExpr(BP.post);
      return neg ? (a.k === "num" ? X.num(-a.v.n, a.v.d) : X.neg(a)) : a;
    }
    return this.parseExpr(BP.post);
  }

  parseIntegral(t) {
    let lo, hi;
    if (this.eat("_")) lo = this.parseBound();
    if (this.eat("^")) hi = this.parseBound();
    if (lo && !hi && this.eat("^")) hi = this.parseBound();
    this.diffStop++;
    const body = this.parseExpr(BP.rel);
    this.diffStop--;
    let v;
    const d = this.peek();
    if (d.t === "id" && d.v === "d") {
      this.next();
      const vt = this.next();
      v = X.sym(vt.v);
    } else {
      v = this.guessVar(body);
      this.warnings.push({ msg: `No differential given; integrating with respect to ${v.name}`, pos: t.s });
    }
    return lo !== undefined ? X.integral(body, v, lo, hi ?? X.OO) : X.integral(body, v);
  }

  parseLimit(t) {
    // lim_(x->a) f, lim x->a f, lim_{x->a^+} f, lim x->0+ f
    this.eat("_");
    const paren = this.eat("(");
    const vt = this.next();
    if (vt.t !== "id") this.err("Limit needs a variable, like lim x->0", vt);
    this.expect("->", "Write the limit as lim x->a f(x)");
    // pull a one-sided marker (^+, ^-, +, -) out of the token stream before parsing the target
    let dir = "";
    for (let j = this.i; j < Math.min(this.toks.length - 1, this.i + 8); j++) {
      const a = this.toks[j], b = this.toks[j + 1], c = this.toks[j + 2] || { t: "eof" };
      const ends = (x) => x.t === "eof" || (x.t === "op" && x.v === ")") || (!paren && this.startsPrimary(x));
      if (a.t === "op" && a.v === "^" && b.t === "op" && (b.v === "+" || b.v === "-") && ends(c)) { dir = b.v; this.toks.splice(j, 2); break; }
      if (!paren && j > this.i && a.t === "op" && a.v === "(") break; // the body has started
      // a bare one-sided sign is glued to the target ("0+ 1/x"); "2 (x^2 - 4)" has a spaced binary minus
      if (a.t === "op" && (a.v === "+" || a.v === "-") && j > this.i && this.toks[j - 1].e === a.s && ends(b) && (paren ? b.v === ")" : true) && !(b.t === "op" && b.v === "(")) {
        if (paren ? b.v === ")" : this.startsPrimary(b) && b.s > a.e) { dir = a.v; this.toks.splice(j, 1); break; }
      }
      if (a.t === "op" && a.v === ")") break;
    }
    this.bound.push(vt.v);
    const to = paren ? this.parseExpr(0) : this.parseExpr(BP.mul);
    this.bound.pop();
    if (paren) this.expect(")");
    const body = this.parseExpr(BP.add);
    return X.limit(body, X.sym(vt.v), to, dir);
  }

  parseBigOp(name, t) {
    // sum_(i=1)^(n) body
    let v, lo, hi;
    if (this.eat("_")) {
      const paren = this.eat("(");
      const vt = this.next();
      v = X.sym(vt.v);
      this.bound.push(vt.v);
      this.expect("=");
      lo = this.parseExpr(BP.rel);
      if (paren) this.expect(")");
    }
    if (this.eat("^")) hi = this.parseExpr(BP.post);
    const body = this.parseExpr(BP.add);
    if (v) this.bound.pop();
    if (!v) this.err(`Write ${name} with bounds, like ${name}_(i=1)^(n) i^2`, t);
    return name === "sum" ? X.sum(body, v, lo, hi ?? X.OO) : X.product(body, v, lo, hi ?? X.OO);
  }
}

export function parseDetailed(src) {
  const text = String(src ?? "").trim();
  if (!text) throw new QuelvraSyntaxError("Nothing to read", 0, "Type an expression or equation");
  if (text.length > 20000) throw new QuelvraSyntaxError("Input is too long (limit 20,000 characters)", 20000);
  const p = new Parser(text);
  const node = applyDefinitions(callForms(p.parseTop(), p.warnings), p.warnings);
  return { node, warnings: p.warnings, congruence: !!p.congruence };
}
export const parse = (src) => parseDetailed(src).node;

// Function-call spellings of calculus operators become the operator nodes:
//   integrate(f, x) / integrate(f, x, a, b), diff(f, x[, n]), limit(f, x, a[, "+"|"-"]),
//   sum(f, i, a, b), prod(f, i, a, b). The variable argument must be a symbol.
function callForms(u, warnings) {
  return X.mapTree(u, (w) => {
    if (w.k !== "fn") return w;
    const a = w.args;
    const isVar = (v) => v && v.k === "sym";
    switch (w.name) {
      case "integrate":
        if ((a.length === 2 || a.length === 4) && isVar(a[1])) return a.length === 2 ? X.integral(a[0], a[1]) : X.integral(a[0], a[1], a[2], a[3]);
        if (a.length === 1) { const fs = [...X.freeSymbols(a[0])]; if (fs.length === 1) { warnings.push(`Integrating with respect to ${fs[0]}.`); return X.integral(a[0], X.sym(fs[0])); } }
        return w;
      case "diff":
        if ((a.length === 2 || a.length === 3) && isVar(a[1]) && (a.length === 2 || X.isInt(a[2]))) return X.deriv(a[0], a[1], a[2] || X.ONE);
        if (a.length === 1) { const fs = [...X.freeSymbols(a[0])]; if (fs.length === 1) return X.deriv(a[0], X.sym(fs[0])); }
        return w;
      case "limit":
        if (a.length === 3 && isVar(a[1])) return X.limit(a[0], a[1], a[2]);
        return w;
      case "sum": case "prod":
        if (a.length === 4 && isVar(a[1])) return (w.name === "sum" ? X.sum : X.product)(a[0], a[1], a[2], a[3]);
        return w;
      default: return w;
    }
  });
}
// "f(x) = x^2; f(3)": definitions f(x) = body followed by items that use f. The uses are expanded
// (f(3) -> 3^2, f'(x) -> d/dx x^2) and the definitions dropped, with a warning naming each one.
// A self-referential definition (a recurrence) or a list of definitions alone is left unchanged.
function applyDefinitions(u, warnings) {
  if ((u.k !== "tuple" && u.k !== "system") || u.args.length < 2) return u;
  const defs = new Map();
  const isDef = (w) => w.k === "eq" && w.args[0].k === "fn" && /^[fgh]$/.test(w.args[0].name) && w.args[0].args.length &&
    w.args[0].args.every((a) => a.k === "sym") && new Set(w.args[0].args.map((a) => a.name)).size === w.args[0].args.length &&
    !X.contains(w.args[1], X.fn(w.args[0].name, ...w.args[0].args)) && !usesFn(w.args[1], w.args[0].name);
  const rest = [];
  for (const w of u.args) {
    if (isDef(w) && !defs.has(w.args[0].name)) defs.set(w.args[0].name, { params: w.args[0].args.map((a) => a.name), body: w.args[1], def: w });
    else rest.push(w);
  }
  if (!defs.size || !rest.length || !rest.some((w) => [...defs.keys()].some((n) => usesFn(w, n)))) return u;
  const expandUses = (w) => X.mapTree(w, (v) => {
    if (v.k !== "fn" || !defs.has(v.name)) return v;
    const d = defs.get(v.name);
    if (v.args.length !== d.params.length) return v;
    return X.subs(d.body, new Map(d.params.map((p, i) => [p, v.args[i]])));
  });
  // definitions may use earlier definitions (g(x) = f(x) + 1)
  for (const d of defs.values()) d.body = expandUses(d.body);
  const out = rest.map(expandUses);
  for (const [name, d] of defs) warnings.push({ msg: `Using the definition ${name}(${d.params.join(", ")}) = ${toText(d.body)}.`, pos: 0 });
  if (out.length === 1) return out[0];
  return out.every((w) => X.isRelation(w) || w.k === "and") ? X.system(...out) : X.tuple(...out);
}
function usesFn(w, name) {
  if (w.k === "fn" && w.name === name) return true;
  return (w.args || []).some((a) => usesFn(a, name));
}

// Words in the source that are not math: letter runs of 3+ letters that are not known names and
// would only parse by being split into single-letter variables ("tell" -> t*e*l*l).
export function unknownWords(src) {
  const text = String(src).replace(/\\(?:begin|end)\{[A-Za-z]+\*?\}/g, " ").replace(/\\[A-Za-z]+/g, " ");
  const out = [];
  for (const m of text.matchAll(/\b(of|is|as|by|if|an|the|to|for|in|with|from|over|where|when|find|what|then|that|than|are|was)\b/gi)) out.push(m[0]);
  for (const m of text.matchAll(/[A-Za-z]{3,}/g)) {
    const w = m[0];
    if (WORDS.includes(w) || WORDS.includes(w.toLowerCase())) continue;
    const parts = splitIdent(w);
    const singles = parts.filter((p) => p.length === 1).length;
    if (singles >= 3 || (singles >= 2 && parts.length === singles && /[aeiou]{1}.*[aeiou]|(.)\1/i.test(w))) out.push(w);
    // "foo", "info", "infant": a word that only splits by borrowing oo (infinity) or inf is not math
    else if (parts.length > 1 && parts.some((p) => p === "oo" || p === "inf")) out.push(w);
    // "form" -> f or m, "band" -> b and: a logic keyword borrowed from inside a longer word is not math
    else if (parts.length > 1 && parts.some((p) => /^(or|and|not|xor|nand|nor|implies|iff)$/i.test(p))) out.push(w);
  }
  return out;
}

