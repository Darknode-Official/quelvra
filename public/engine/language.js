// Quelvra language engine: translates English math requests into Quelvra input text.
//
// It only TRANSLATES. It never computes an answer. Output:
//   { ok, math, goal, variable, interpretation, pattern, confidence, notes }
// or { ok: false, reason } when the sentence is not understood (it refuses to guess).
// The UI always shows `interpretation` so the user can see and correct what was understood.
// Readings that involve a convention (log without a base, "area under" as a signed integral,
// a default series order) say so in `notes`.
//
// Function-analysis requests become command calls that the analysis strategies implement:
//   domain(f, x)  range(f, x)  zeros(f, x)  intercepts(f, x)  asymptotes(f, x)  extrema(f, x[, a, b])
//   inflection(f, x)  monotonic(f, x)  critical(f, x)  tangent(f, x, a)  normal(f, x, a)  inverse(f, x)
//   completesquare(p, x)  apart(p, x)  identity(lhs, rhs)  line/slope/distance/midpoint(x1, y1, x2, y2)
//   arclength(f, x, a, b)  areabetween(f, g, x[, a, b])  volume(f, x, a, b)  avgvalue(f, x, a, b)
//   maximize(f, x[, a, b])  minimize(f, x[, a, b])  (solve/optimize.js reads these call forms)
// "f(x) = <expr>" or "y = <expr>" in such a request passes <expr> as f and x as the variable.

import { parse, FUNCTIONS, latexToText } from "./parse.js";
import { morePatterns, TAIL } from "./language-more.js";
import { wordPatterns } from "./language-words.js";

const NUMBER_WORDS = {
  zero: 0, one: 1, two: 2, three: 3, four: 4, five: 5, six: 6, seven: 7, eight: 8, nine: 9, ten: 10,
  eleven: 11, twelve: 12, thirteen: 13, fourteen: 14, fifteen: 15, sixteen: 16, seventeen: 17, eighteen: 18, nineteen: 19,
  twenty: 20, thirty: 30, forty: 40, fifty: 50, sixty: 60, seventy: 70, eighty: 80, ninety: 90,
};
const SCALES = { hundred: 100, thousand: 1000, million: 1e6, billion: 1e9 };
const MULT_WORDS = { twice: 2, double: 2, triple: 3, thrice: 3, half: "1/2", quadruple: 4 };
const ORDINAL_DEN = { half: 2, halves: 2, third: 3, thirds: 3, quarter: 4, quarters: 4, fourth: 4, fourths: 4, fifth: 5, fifths: 5, sixth: 6, sixths: 6, eighth: 8, eighths: 8, tenth: 10, tenths: 10 };
const ORDER_WORDS = { first: 1, "1st": 1, second: 2, "2nd": 2, third: 3, "3rd": 3, fourth: 4, "4th": 4, fifth: 5, "5th": 5 };

// "twenty five" -> "25", "three hundred and two" -> "302", "two thirds" -> "(2/3)"
export function wordsToNumbers(s) {
  const toks = s.split(/(\s+|-)/);
  const out = [];
  let acc = null, cur = 0;
  const flush = () => { if (acc !== null || cur) { out.push(String((acc || 0) + cur), " "); } acc = null; cur = 0; };
  for (let i = 0; i < toks.length; i++) {
    const t = toks[i], w = t.toLowerCase();
    if (/^\s+$|^-$/.test(t)) { if (acc === null && !cur) out.push(t); continue; }
    if (w in NUMBER_WORDS) { cur += NUMBER_WORDS[w]; continue; }
    if (w in SCALES && (cur || acc !== null)) { const sc = SCALES[w]; if (sc === 100) cur *= 100; else { acc = (acc || 0) + (cur || 1) * sc; cur = 0; } continue; }
    if (w === "and" && (cur || acc !== null) && toks[i + 2] && toks[i + 2].toLowerCase() in NUMBER_WORDS) continue;
    if (w in ORDINAL_DEN && (cur || acc !== null)) { const n = (acc || 0) + cur; acc = null; cur = 0; out.push(` (${n}/${ORDINAL_DEN[w]}) `); continue; }
    flush();
    out.push(t);
  }
  flush();
  return out.join("").replace(/\s+/g, " ").trim();
}

// "(x + 1) squared" / "x squared": the operand is the balanced group or the token before the word
function powerWords(s) {
  const WORDS = [[/^ raised to the power of (\S+)/, null], [/^ raised to the (\S+?)(?:st|nd|rd|th)? power\b/, null], [/^ raised to (\S+)/, null],
    [/^ squared\b/, "2"], [/^ cubed\b/, "3"], [/^ to the power of (\S+)/, null], [/^ to the power (\S+)/, null], [/^ to the (\d+)(?:st|nd|rd|th)(?: power)?\b/, null]];
  for (let guard = 0; guard < 20; guard++) {
    let hit = null;
    for (const [re, e] of WORDS) {
      for (let i = 0; i < s.length; i++) {
        if (s[i] !== " ") continue;
        const m = s.slice(i).match(re);
        if (!m) continue;
        // operand ending at i
        let j = i - 1;
        if (j < 0) continue;
        let start;
        if (s[j] === ")") {
          let depth = 0;
          for (start = j; start >= 0; start--) { if (s[start] === ")") depth++; else if (s[start] === "(") { depth--; if (depth === 0) break; } }
          if (start < 0) continue;
          while (start > 0 && /[A-Za-z0-9_]/.test(s[start - 1])) start--; // f(x) squared, sqrt(x) squared
        } else {
          start = j;
          while (start > 0 && /[^\s()]/.test(s[start - 1])) start--;
        }
        const base = s.slice(start, i);
        if (!base) continue;
        hit = { start, end: i + m[0].length, text: `(${base})^(${e || m[1]})` };
        break;
      }
      if (hit) break;
    }
    if (!hit) break;
    s = s.slice(0, hit.start) + hit.text + s.slice(hit.end);
  }
  return s;
}

// Phrase-level operator translation (applied to already-numeric text).
const PHRASES = [
  [/\bthe square root of\b/g, "sqrt "], [/\bsquare root of\b/g, "sqrt "], [/\bthe cube root of\b/g, "cbrt "], [/\bcube root of\b/g, "cbrt "],
  [/\b(?:the )?natural log(?:arithm)? of\b/g, "ln "], [/\blog(?:arithm)? base (\S+) of\b/g, "log_$1 "], [/\b(?:the )?log(?:arithm)? of\b/g, "log "],
  [/\b(?:the )?absolute value of\b/g, "abs "], [/\b(?:the )?factorial of\b/g, "factorial "], [/(\d|\))\s*factorial\b/g, "$1!"],
  [/\bthe square of (\S+)/g, "($1)^2"], [/\bthe cube of (\S+)/g, "($1)^3"], [/\be to the (?!power\b)(\S+)/g, "e^($1)"],
  [/\bnegative (?=\d|[a-z]\b|\()/g, "-"], [/\bmodulo\b/g, "mod"],
  [/\bplus\b/g, "+"], [/\bminus\b/g, "-"], [/\btimes\b/g, "*"], [/\bmultiplied by\b/g, "*"], [/\bdivided by\b/g, "/"], [/\bover\b/g, "/"],
  [/\bis greater than or equal to\b/g, ">="], [/\bis less than or equal to\b/g, "<="], [/\bis at least\b/g, ">="], [/\bis at most\b/g, "<="],
  [/\bis greater than\b/g, ">"], [/\bis less than\b/g, "<"], [/\bis more than\b/g, ">"], [/\bis not equal to\b/g, "!="],
  [/\bgreater than or equal to\b/g, ">="], [/\bless than or equal to\b/g, "<="], [/\bgreater than\b/g, ">"], [/\bless than\b/g, "<"],
  [/\bequals\b/g, "="], [/\bis equal to\b/g, "="], [/\bequal to\b/g, "="], [/\bpi\b/g, "pi"],
  [/\bsine of\b/g, "sin "], [/\bcosine of\b/g, "cos "], [/\btangent of\b/g, "tan "], [/\bsin of\b/g, "sin "], [/\bcos of\b/g, "cos "], [/\btan of\b/g, "tan "],
  [/\bdegrees?\b/g, "°"],
  // quantities of: half of 10, a third of 9, (2/3) of 9, twice 7, 20% of 50
  [/\b(?:one |a )?half of\b/g, "(1/2)*"], [/\ba third of\b/g, "(1/3)*"], [/\ba quarter of\b/g, "(1/4)*"], [/(\(\d+\/\d+\)) of\b/g, "$1*"],
  [/\btwice\b/g, "2*"], [/\bdouble\b/g, "2*"], [/\btriple\b/g, "3*"], [/(\S+?) ?(?:%|percent) of (\S+)/g, "($1/100)*($2)"], [/\bpercent\b/g, "%"],
  // the sum / product / difference / quotient of A and B (single tokens after the rewrites above)
  [/\b(?:the )?sum of ((?:\S+, )*\S+?),? and (\S+)/g, (m, a, b) => `(${a.split(/, /).join(" + ")} + ${b})`],
  [/\b(?:the )?product of ((?:\S+, )*\S+?),? and (\S+)/g, (m, a, b) => `(${a.split(/, /).map((t) => `(${t})`).join("*")}*(${b}))`],
  [/\b(?:the )?difference (?:between|of) (\S+) and (\S+)/g, "(($1) - ($2))"], [/\b(?:the )?quotient of (\S+) and (\S+)/g, "(($1)/($2))"],
];
function phrases(s) {
  let t = powerWords(s);
  for (const [re, rep] of PHRASES) t = t.replace(re, rep);
  return t.replace(/\s+/g, " ").trim();
}

const MATH_UNICODE = "≤≥≠±∓·×÷−–∞πθ√∛∜∫∑∏∂⌊⌋⌈⌉⟨⟩≡°²³¹⁰⁴⁵⁶⁷⁸⁹⁻⁺ⁿⁱˣ₀₁₂₃₄₅₆₇₈₉½⅓⅔¼¾αβγδεζηλμνξρστφϕχψωΔΩΣ→′";
const MATHY = new RegExp(`^[\\s\\d.a-z+\\-*/^()=<>!,;:|°%\\[\\]{}_'${MATH_UNICODE}]*$`, "i");
const UNIT_WORDS = ["km", "mi", "min", "ft", "cm", "mm", "kg", "lb", "degf", "degc", "mph"];
const KNOWN_WORDS = new Set([...[...FUNCTIONS].map((w) => w.toLowerCase()), "pi", "oo", "inf", "infinity", "int", "lim", "sum", "prod", "and", "or", "not", "theta", "alpha", "beta",
  "gamma", "lambda", "mu", "sigma", "phi", "omega", "delta", "epsilon", "rho", "tau", "psi", "chi", "eta", "zeta", "deg", "log_2", "log_10", "arcsin", "arccos", "arctan", ...UNIT_WORDS]);
// English words that are never products of variables in a request
const STOP = /\b(?:of|is|are|as|to|from|for|by|if|when|what|whats|how|find|with|at|in|on|up|me|my|we|us|it|am|be|do|go|so|no|hi|ok|you|your|he|she|his|her|the|an|this|that)\b/i;
// True when s is written in math notation: characters are mathematical, every word of three or
// more letters is a known function / constant, and the parser accepts it.
function looksLikeMath(s0) {
  let s = s0;
  if (/\\[A-Za-z]/.test(s)) {
    if (/\\(?:text|mbox)\{[^}]*[A-Za-z]{3,}/.test(s)) return false;
    try { s = latexToText(s); } catch (_) { return false; }
    s = s.replace(/[&]/g, " ");
  }
  if (!MATHY.test(s)) return false;
  if (STOP.test(s)) return false;
  // command words count as math only in call form: factor(x^2 - 1), not "factor x^2 - 1"
  if (/\b(?:solve|simplify|expand|factor|integrate|diff|derivative|plot|mean|median|mode|variance|stdev|gcd|lcm)\b(?!\()/i.test(s)) return false;
  const words = s.toLowerCase().match(/[a-z_0-9]*[a-z]{3,}[a-z_0-9]*/g) || [];
  if (words.map((w) => (/^log_/.test(w) ? w : w.replace(/_.*$/, ""))).some((w) => w && !KNOWN_WORDS.has(w) && !/^log_/.test(w) && !/^d[a-z]$/.test(w) && !/^\d/.test(w))) return false;
  try { parse(s0); return true; } catch (_) { return false; }
}
// trailing sentence punctuation; "!" only after a word (so 5! and n! stay factorials)
const clean = (s) => s.replace(/(?<=[A-Za-z]{2})!+$/, "").replace(/[?.]+$/, "").trim();

// ---------------------------------------------------------------- helpers
function expr(s) { return phrases(wordsToNumbers(s)).replace(/^\s*the\s+/i, ""); }
function list(a, b) { return [a, b].filter(Boolean).join(",").split(/\s*(?:,|\band\b)\s*/).map((t) => expr(t)).filter(Boolean).join(", "); }
function paren(k) { return /^\d+$/.test(String(k)) ? String(k) : `(${k})`; }
// distance / time / rate units for the travel word problems: [kind, name, base length or time]
const TRAVEL_UNITS = { km: ["len", "km"], kilometers: ["len", "km"], kilometres: ["len", "km"], miles: ["len", "mi"], mile: ["len", "mi"], mi: ["len", "mi"],
  m: ["len", "m"], meters: ["len", "m"], metres: ["len", "m"], hours: ["time", "h"], hour: ["time", "h"], h: ["time", "h"], hr: ["time", "h"], hrs: ["time", "h"],
  minutes: ["time", "min"], minute: ["time", "min"], min: ["time", "min"], seconds: ["time", "s"], second: ["time", "s"], s: ["time", "s"] };
const RATE_UNITS = { "km/h": ["km", "h"], kph: ["km", "h"], kmh: ["km", "h"], mph: ["mi", "h"], "mi/h": ["mi", "h"], "m/s": ["m", "s"] };
const unitOf = (u, kind) => { const t = TRAVEL_UNITS[String(u).toLowerCase()]; return t && t[0] === kind ? t[1] : null; };
const rateOf = (u) => RATE_UNITS[String(u).toLowerCase()] || null;
// the variable of an expression: its free symbols from the parse tree (so e, pi and i, which are
// constants, never qualify), preferring x, then t, y, z
function guessVar(s) {
  const found = new Set();
  const walk = (u) => { if (!u) return; if (u.k === "sym") found.add(u.name); for (const a of u.args || []) walk(a); };
  try { walk(parse(s)); } catch (_) { const m = s.match(/\b([a-df-hj-z])\b/i); return m ? m[1] : "x"; }
  for (const v of ["x", "t", "y", "z", "u", "v", "theta", "s", "n"]) if (found.has(v)) return v;
  return [...found].sort()[0] || "x";
}
// "f(x) = x^2", "y = x^2", "the function x^2", "the curve y = sin x" -> { f, x } with f in math text
function fnOf(s0) {
  let s = expr(String(s0).trim().replace(/^(?:the )?(?:function|curve|graph of|graph|expression|polynomial|rational function)\s+/i, ""));
  let x = null, m;
  if ((m = s.match(/^([a-zA-Z])\s*\(\s*([a-z]|theta)\s*\)\s*=\s*(.+)$/))) { x = m[2]; s = m[3]; }
  else if ((m = s.match(/^y\s*=\s*(.+)$/))) s = m[1];
  s = s.trim();
  if (!s || /[=<>]/.test(s) || !looksLikeMath(s)) return null;
  return { f: s, x: x || guessVar(s) };
}
function mathOf(s0) { const s = expr(String(s0).trim()); return s && looksLikeMath(s) ? s : null; }
// trailing interval clause: "... from a to b", "... on [a, b]", "... between x = a and x = b", "... for a <= x <= b"
function splitInterval(s) {
  let m;
  if ((m = s.match(/^(.+?),? (?:on|over|in) (?:the )?(?:closed )?(?:interval )?\[\s*(.+?)\s*,\s*(.+?)\s*\]$/i))) return { body: m[1], a: m[2], b: m[3] };
  if ((m = s.match(/^(.+?),? (?:from|between) (?:[a-z] ?= ?)?(.+?) (?:to|and) (?:[a-z] ?= ?)?(.+)$/i))) return { body: m[1], a: m[2], b: m[3] };
  if ((m = s.match(/^(.+?),? for (.+?) <=? ([a-z]) <=? (.+)$/i))) return { body: m[1], a: m[2], b: m[4] };
  return { body: s };
}
function bound(s) {
  const t = String(s).trim();
  if (/^(?:positive )?infinity$/i.test(t)) return "oo";
  if (/^(?:negative|minus) infinity$/i.test(t)) return "-oo";
  return mathOf(t);
}
const LEAD = String.raw`(?:(?:find|compute|calculate|determine|what is|what's|whats|what are|give|state|evaluate|get|show|list|identify|sketch and find) )?(?:me )?(?:all )?(?:the )?`;
const re = (src, flags = "i") => new RegExp(src, flags);
const POINT = String.raw`\(\s*([^,()]+?)\s*,\s*([^,()]+?)\s*\)`;
// analysis command on a function, with an optional interval
function analysis(cmd, s, { interval = "optional", label } = {}) {
  const iv = interval === "none" ? { body: s } : splitInterval(s);
  if (interval === "required" && iv.a === undefined) return null;
  const fx = fnOf(iv.body);
  if (!fx) return null;
  let a = null, b = null;
  if (iv.a !== undefined) { a = bound(iv.a); b = bound(iv.b); if (!a || !b) return null; }
  const args = [fx.f, fx.x, ...(a ? [a, b] : [])];
  return { math: `${cmd}(${args.join(", ")})`, goal: cmd, variable: fx.x, interpretation: `${label || cmd} of ${fx.f}${a ? ` for ${fx.x} from ${a} to ${b}` : ""}` };
}
// "A and B" joined equations -> system text "A, B" (only when every part is an equation)
function equationsText(s) {
  const parts = s.split(/\s*(?:;|,(?![^()[\]]*[)\]])|\band\b)\s*/i).map((p) => expr(p)).filter(Boolean);
  if (parts.length > 1 && parts.every((p) => /=/.test(p) && !/[<>]/.test(p))) return parts.join(", ");
  return expr(s);
}

// Patterns: each returns a translation or null. Ordered from most to least specific.
// ---- advanced continuous commands (engine/advanced/language-patterns.js): first, each steps aside when not applicable ----
import { advancedPatterns } from "./advanced/language-patterns.js";
const PATTERNS = [
  ...advancedPatterns({ expr, mathOf, bound, splitInterval, guessVar, looksLikeMath, fnOf }),
  // ---- end advanced continuous commands ----
  // whole word problems (ages, mixtures, rates, interest, consecutive integers, ...): language-words.js
  ...wordPatterns({ wordsToNumbers }),
  // probability, statistics, counting, complex numbers, series, geometry, number theory, ... (language-more.js)
  ...morePatterns({ expr, mathOf, LEAD, re }),
  // ---- differential equations and systems ----
  { id: "solve-ode", re: /^solve (?:the )?(?:differential )?(?:equation )?(.+?) (?:with|given|where|if|subject to|and) (?:the )?(?:initial (?:conditions?|values?) )?((?:[a-z]'*\(.+?\) ?= ?.+?)(?:(?:,| and) [a-z]'*\(.+?\) ?= ?.+?)*)$/i,
    build: (m) => { if (!/'|d[a-z]\/d[a-z]/.test(m[1])) return null; const conds = m[2].split(/\s*(?:,|\band\b)\s*/).map(expr); const math = [expr(m[1]), ...conds].join(", ");
      return { math, goal: "solve", interpretation: `solve the differential equation ${expr(m[1])} with ${conds.join(", ")}` }; } },
  { id: "solve-system", re: /^solve (?:the )?(?:system|simultaneous equations|linear system)(?: of (?:linear )?equations)?:? (.+)$/i,
    build: (m) => { const math = equationsText(m[1]); return /,/.test(math) ? { math, goal: "solve", interpretation: `solve the system ${math}` } : null; } },
  { id: "solve-for", re: /^solve for ([a-z]|theta)[:,]? (.+)$/i, build: (m) => ({ math: equationsText(m[2]), goal: "solve", variable: m[1], interpretation: `solve ${expr(m[2])} for ${m[1]}` }) },
  { id: "solve-for", re: /^(?:solve|find) (.+?) for ([a-z])$/i, build: (m) => ({ math: expr(m[1]), goal: "solve", variable: m[2], interpretation: `solve ${expr(m[1])} for ${m[2]}` }) },
  { id: "solve-value", re: /^(?:find|what is|what's|determine|compute) (?:the value of )?([a-z]) (?:if|when|given|given that|such that|where|so that):? (.+)$/i,
    build: (m) => ({ math: equationsText(m[2]), goal: "solve", variable: m[1], interpretation: `solve ${equationsText(m[2])} for ${m[1]}` }) },
  { id: "solve-value", re: /^find ([a-z]): (.+)$/i, build: (m) => ({ math: equationsText(m[2]), goal: "solve", variable: m[1], interpretation: `solve ${equationsText(m[2])} for ${m[1]}` }) },
  { id: "solve-when", re: /^for (?:what|which) (?:values? of |real )?([a-z]) (?:is|are|does|do) (.+)$/i,
    build: (m) => ({ math: expr(m[2]), goal: "solve", variable: m[1], interpretation: `solve ${expr(m[2])} for ${m[1]}` }) },
  { id: "solve-when", re: /^when (?:does|is|do|will) (.+?) (?:equal|equals|=|become|reach) (.+)$/i,
    build: (m) => { const l = expr(m[1]), r = expr(m[2]); return { math: `${l} = ${r}`, goal: "solve", interpretation: `solve ${l} = ${r}` }; } },
  { id: "solve-when", re: /^when is (.+?[=<>].+)$/i, build: (m) => ({ math: expr(m[1]), goal: "solve", interpretation: `solve ${expr(m[1])}` }) },
  { id: "roots", re: re(`^${LEAD}(?:real )?(?:roots|solutions?|root) (?:of|to|for) (?:the (?:equation|polynomial) )?(.+)$`),
    build: (m) => { const t = expr(m[1]); if (/[<>]/.test(t)) return null; const math = /=/.test(t) ? t : `${t} = 0`; return { math, goal: "solve", interpretation: `solve ${math}` }; } },

  // ---- function analysis ----
  { id: "domain", re: re(`^${LEAD}domain (?:of|for) (.+)$`), build: (m) => analysis("domain", m[1], { interval: "none" }) },
  { id: "range", re: re(`^${LEAD}range (?:of|for) (.+)$`), build: (m) => analysis("range", m[1], { interval: "none" }) },
  { id: "zeros", re: re(`^${LEAD}(?:real )?(?:zeros|zeroes|zero) (?:of|for) (.+)$`), build: (m) => analysis("zeros", m[1], { interval: "none" }) },
  { id: "intercepts", re: re(`^${LEAD}(?:(?:x|y)[- ]?intercepts?|intercepts?|(?:x|y)[- ]?axis intercepts?) (?:of|for) (.+)$`), build: (m) => analysis("intercepts", m[1], { interval: "none" }) },
  { id: "asymptotes", re: re(`^${LEAD}(?:vertical |horizontal |oblique |slant )?(?:and (?:vertical |horizontal |oblique |slant ))?asymptotes? (?:of|for) (.+)$`),
    build: (m) => { const r = analysis("asymptotes", m[1], { interval: "none" }); if (r) r.notes = ["All asymptotes (vertical, horizontal and oblique) are found."]; return r; } },
  { id: "critical", re: re(`^${LEAD}critical (?:points|point|numbers|number|values|value) (?:of|for) (.+)$`), build: (m) => analysis("critical", m[1], { interval: "none", label: "critical points" }) },
  { id: "inflection", re: re(`^${LEAD}(?:inflection points?|points? of inflection|inflexion points?) (?:of|for) (.+)$`), build: (m) => analysis("inflection", m[1], { interval: "none", label: "inflection points" }) },
  { id: "extrema", re: re(`^${LEAD}(?:local |relative )?(?:extrema|extreme values|extreme points|turning points|stationary points|maxima and minima|minima and maxima|maximum and minimum(?: values| points)?|minimum and maximum(?: values| points)?|max and min|local maximum|local minimum|local maxima|local minima|relative maximum|relative minimum) (?:values )?(?:of|for) (.+)$`),
    build: (m) => analysis("extrema", m[1], { label: "extrema" }) },
  { id: "optimize", re: re(`^${LEAD}(?:absolute |global )?(maximum|minimum|max|min|largest value|smallest value|greatest value|least value)(?: values?)? (?:of|for) (.+)$`),
    build: (m) => { const cmd = /max|larg|great/i.test(m[1]) ? "maximize" : "minimize"; return analysis(cmd, m[2], { label: cmd === "maximize" ? "maximum" : "minimum" }); } },
  { id: "optimize", re: /^(maximi[sz]e|minimi[sz]e) (.+)$/i,
    build: (m) => { if (/\bsubject to\b|\bconstraint\b/i.test(m[2])) return null; const cmd = /^max/i.test(m[1]) ? "maximize" : "minimize"; return analysis(cmd, m[2]); } },
  { id: "monotonic", re: /^(?:where|when|on what intervals?|on which intervals?|over what intervals?|for what values of [a-z]) (?:is|are|does|do) (.+?) (increasing|decreasing|increase|decrease|rising|falling)$/i,
    build: (m) => analysis("monotonic", m[1], { interval: "none", label: "intervals of increase and decrease" }) },
  { id: "monotonic", re: /^(?:find )?(?:the )?intervals? (?:where|on which|over which) (.+?) (?:is|are) (increasing|decreasing)$/i,
    build: (m) => analysis("monotonic", m[1], { interval: "none", label: "intervals of increase and decrease" }) },
  { id: "monotonic", re: re(`^${LEAD}(?:intervals of (?:increase|decrease)(?: and (?:increase|decrease))?|increasing and decreasing intervals|intervals where the function is increasing|monotonicity) (?:of|for) (.+)$`),
    build: (m) => analysis("monotonic", m[1], { interval: "none", label: "intervals of increase and decrease" }) },
  { id: "tangent", re: re(`^${LEAD}(?:equation (?:of|for) (?:the )?)?(tangent|normal)(?: line)? (?:line )?(?:to|of|for|at) (?:the (?:curve|graph|function) )?(?:of )?(.+?) at (?:the point )?(?:where )?(.+)$`),
    build: (m) => {
      const cmd = m[1].toLowerCase();
      const fx = fnOf(m[2]);
      if (!fx) return null;
      let pt = m[3].trim(), mm;
      if ((mm = pt.match(/^\(\s*([^,()]+?)\s*,\s*([^,()]+?)\s*\)$/))) pt = mm[1];
      else if ((mm = pt.match(/^([a-z])\s*=\s*(.+)$/i))) { if (mm[1] !== fx.x) return null; pt = mm[2]; }
      const a = mathOf(pt);
      if (!a) return null;
      return { math: `${cmd}(${fx.f}, ${fx.x}, ${a})`, goal: cmd, variable: fx.x, interpretation: `${cmd} line to ${fx.f} at ${fx.x} = ${a}` };
    } },
  { id: "matrix", re: re(`^${LEAD}(determinant|det|inverse|eigenvalues|eigenvectors|transpose|rank|trace|rref|reduced row echelon form) (?:of )?(?:the )?(?:matrix )?(\\[.+\\])$`),
    build: (m) => { const f = { determinant: "det", det: "det", inverse: "inv", "reduced row echelon form": "rref" }[m[1].toLowerCase()] || m[1].toLowerCase(); const M = mathOf(m[2]);
      return M ? { math: `${f}(${M})`, goal: "evaluate", interpretation: `${m[1].toLowerCase()} of ${M}` } : null; } },
  { id: "inverse", re: re(`^${LEAD}inverse(?: function)? (?:of|for) (?:the function )?(.+)$`), build: (m) => analysis("inverse", m[1], { interval: "none", label: "inverse function" }) },
  { id: "completesquare", re: /^(?:complete|completing) the square(?: (?:for|of|in|on))? (.+)$/i,
    build: (m) => { const t = expr(m[1]); if (/[<>]/.test(t)) return null; const eqm = t.match(/^(.+?)=(.+)$/); const p = eqm ? `${eqm[1].trim()} - (${eqm[2].trim()})` : t;
      const r = analysis("completesquare", p, { interval: "none", label: "completed square" }); if (r && eqm) r.notes = ["Completing the square of the left side minus the right side."]; return r; } },
  { id: "apart", re: re(`^${LEAD}partial fractions?(?: decomposition| expansion| form)? (?:of|for) (.+)$`), build: (m) => analysis("apart", m[1], { interval: "none", label: "partial fractions" }) },
  { id: "apart", re: /^(?:decompose|split|write|express) (.+?) (?:into|in|as) partial fractions$/i, build: (m) => analysis("apart", m[1], { interval: "none", label: "partial fractions" }) },
  { id: "identity", re: /^(?:prove|show|verify|check|confirm|test)(?: that| whether| if)? (.+?)(?: is an identity| is always true| is true for all [a-z]| for all [a-z]| holds for all [a-z])?$/i,
    build: (m) => identityOf(m[1]) },
  { id: "identity", re: /^is (.+?) (?:an identity|always true|true for all [a-z]|identically true)$/i, build: (m) => identityOf(m[1]) },
  { id: "points", re: re(`^${LEAD}(slope|gradient|distance|midpoint|mid-point|mid point)(?: of the (?:line|segment)(?: (?:through|joining|between|passing through))?)?(?: (?:between|of|from|through|joining|passing through|connecting))? ?${POINT} (?:and|to) ${POINT}$`),
    build: (m) => points({ slope: "slope", gradient: "slope", distance: "distance" }[m[1].toLowerCase()] || "midpoint", m.slice(2, 6)) },
  { id: "points", re: re(`^${LEAD}(?:equation (?:of|for) )?(?:the )?(?:straight )?line (?:through|passing through|between|joining|containing|connecting|that passes through|that goes through|going through) (?:the points )?${POINT} and ${POINT}$`),
    build: (m) => points("line", m.slice(1, 5)) },
  { id: "arclength", re: re(`^${LEAD}(?:arc ?length|length of the (?:curve|arc|graph)|length of the arc) (?:of )?(.+)$`), build: (m) => analysis("arclength", m[1], { interval: "required", label: "arc length" }) },
  { id: "areabetween", re: re(`^${LEAD}area (?:of the region )?(?:between|bounded by|enclosed by|enclosed between) (?:the (?:curves|graphs) )?(?:of )?(.+)$`),
    build: (m) => {
      const iv = splitInterval(m[1]);
      const parts = iv.body.split(/\s+and\s+/i);
      if (parts.length !== 2) return null;
      const f = fnOf(parts[0]), g = fnOf(parts[1]);
      if (!f || !g) return null;
      const x = guessVar(`${f.f} + ${g.f}`);
      let tail = "";
      if (iv.a !== undefined) { const a = bound(iv.a), b = bound(iv.b); if (!a || !b) return null; tail = `, ${a}, ${b}`; }
      return { math: `areabetween(${f.f}, ${g.f}, ${x}${tail})`, goal: "areabetween", variable: x, interpretation: `area between ${f.f} and ${g.f}${tail ? ` for ${x} from ${tail.slice(2).replace(", ", " to ")}` : " (between their intersections)"}` };
    } },
  { id: "area-under", re: re(`^${LEAD}area (?:under|beneath|below) (?:the (?:curve|graph) )?(?:of )?(.+)$`),
    build: (m) => { const r = analysis("integrate", m[1], { interval: "required", label: "integral" }); if (!r) return null;
      return { ...r, goal: "integrate", notes: ["Computed as the definite integral (signed area: parts below the axis count as negative)."] }; } },
  { id: "volume", re: re(`^${LEAD}volume (?:of )?(.+)$`),
    build: (m) => {
      let t = m[1];
      if (/\b(?:about|around) (?:the )?(?:line |y[- ]?axis|x ?= ?|y ?= ?)/i.test(t)) return null; // only rotation about the x-axis is supported
      t = t.replace(/,?\s*(?:about|around) (?:the )?x[- ]?axis/i, "");
      t = t.replace(/^(?:the )?(?:solid )?(?:of revolution )?(?:revolution )?(?:(?:formed|generated|obtained|made|produced) )?(?:(?:by|when) )?(?:rotating |revolving )?(?:the region (?:under|below) )?(?:of |for )?/i, "");
      const r = analysis("volume", t, { interval: "required", label: "volume of revolution about the x-axis" });
      if (r) r.notes = ["Rotation about the x-axis (disk method)."];
      return r;
    } },
  { id: "avgvalue", re: re(`^${LEAD}average value of (.+)$`), build: (m) => analysis("avgvalue", m[1], { interval: "required", label: "average value" }) },
  { id: "vector-product", re: re(`^${LEAD}(dot|scalar|cross|vector) product of (.+?) and (.+)$`),
    build: (m) => { const f = /dot|scalar/i.test(m[1]) ? "dot" : "cross"; const a = mathOf(m[2]), b = mathOf(m[3]); return a && b ? { math: `${f}(${a}, ${b})`, goal: "evaluate", interpretation: `${f} product of ${a} and ${b}` } : null; } },
  { id: "series", re: re(`^${LEAD}(taylor|maclaurin|power) (?:series|polynomial|expansion)(?: expansion)? (?:of|for) (.+)$`), build: (m) => seriesOf(m[2], m[1].toLowerCase() === "maclaurin", true) },
  { id: "series", re: re(`^${LEAD}series(?: expansion)? (?:of|for) (.+)$`), build: (m) => seriesOf(m[1], false, false) },

  // ---- calculus ----
  { id: "derivative", re: re(`^${LEAD}(?:(first|second|third|fourth|fifth|1st|2nd|3rd|4th|5th) )?(?:partial )?derivative of (.+?)(?: with respect to ([a-z]|theta))?$`),
    build: (m) => { const ord = ORDER_WORDS[(m[1] || "first").toLowerCase()]; const fx = fnOf(m[2]); if (!fx) return null; const v = m[3] || fx.x; return deriv(fx.f, v, ord); } },
  { id: "derivative", re: /^(?:find |compute |what is |evaluate )?d\/d([a-z]) (?:of )?(.+)$/i, build: (m) => { const fx = fnOf(m[2]); return fx ? deriv(fx.f, m[1], 1) : null; } },
  { id: "derivative", re: /^(?:find|compute|what is|what's|determine|calculate) ([a-z])('+)\(([a-z])\) (?:if|when|for|given|where) \1\(\3\) ?= ?(.+)$/i,
    build: (m) => { const f = mathOf(m[4]); return f ? deriv(f, m[3], m[2].length) : null; } },
  { id: "derivative", re: /^(?:find|compute|what is|what's|determine|calculate) d([a-z])\/d([a-z]) (?:if|when|for|given|where) \1 ?= ?(.+)$/i,
    build: (m) => { const f = mathOf(m[3]); return f ? deriv(f, m[2], 1) : null; } },
  { id: "differentiate", re: /^differentiate (.+?)(?: with respect to ([a-z]|theta))?$/i,
    build: (m) => { const fx = fnOf(m[1]); if (!fx) return null; return { ...deriv(fx.f, m[2] || fx.x, 1), pattern: "differentiate" }; } },
  { id: "integral-def", re: re(`^${LEAD}(?:definite )?integral from (.+?) to (.+?) of (.+?)(?: d([a-z]))?(?: with respect to ([a-z]))?$`),
    build: (m) => integralOf(m[3], m[4] || m[5], m[1], m[2]) },
  { id: "integral-def", re: re(`^${LEAD}(?:definite )?integral of (.+?) (?:from|between) (.+?) (?:to|and) (.+?)(?: with respect to ([a-z]))?$`),
    build: (m) => integralOf(m[1], m[4], m[2], m[3]) },
  { id: "integral-def", re: re(`^${LEAD}(?:definite )?integral of (.+?) (?:on|over) \\[(.+?),(.+?)\\]$`), build: (m) => integralOf(m[1], null, m[2], m[3]) },
  { id: "integral", re: re(`^${LEAD}(?:indefinite )?(?:integral|antiderivative|anti-derivative|primitive) of (.+?)(?: with respect to ([a-z]))?$`),
    build: (m) => integralOf(m[1], m[2]) },
  { id: "integrate", re: /^integrate (.+?)(?: (?:from|between) (.+?) (?:to|and) (.+?))?(?: with respect to ([a-z]))?$/i,
    build: (m) => integralOf(m[1], m[4], m[2], m[3]) },
  { id: "limit", re: re(`^${LEAD}limit of (.+?) as ([a-z]) (?:approaches|goes to|tends to|tends towards|->|→) (.+?)(?: from (?:the )?(left|right|above|below))?$`),
    build: (m) => limitOf(m[1], m[2], m[3], m[4]) },
  { id: "limit", re: re(`^${LEAD}(?:limit|lim) as ([a-z]) (?:approaches|goes to|tends to|->|→) (.+?)(?: from (?:the )?(left|right|above|below))? of (.+)$`),
    build: (m) => limitOf(m[4], m[1], m[2], m[3]) },
  { id: "sum-index", re: re(`^${LEAD}(sum|product) (?:of )?(.+?) (?:from|for) ([a-z]) ?= ?(.+?) to (.+)$`),
    build: (m) => bigOp(m[1], m[2], m[3], m[4], m[5]) },
  { id: "sum-index", re: re(`^${LEAD}(sum|product) (?:from|for) ([a-z]) ?= ?(.+?) to (.+?) of (.+)$`),
    build: (m) => bigOp(m[1], m[5], m[2], m[3], m[4]) },

  // ---- arithmetic and number theory ----
  { id: "percent-of", re: /^(?:what is |what's |find |calculate )?(\S+?) ?(?:%|percent) of (\S+)$/i,
    build: (m) => ({ math: `${m[1]}/100 * ${m[2]}`, goal: "evaluate", interpretation: `${m[1]}% of ${m[2]}` }) },
  { id: "what-percent", re: /^(\S+) is what (?:%|percent) of (\S+)$/i,
    build: (m) => ({ math: `p/100 * ${m[2]} = ${m[1]}`, goal: "solve", variable: "p", interpretation: `find p with p% of ${m[2]} = ${m[1]}` }) },
  { id: "percent-change", re: /^(?:what is the )?percent(?:age)? (?:change|increase|decrease) from (\S+) to (\S+)$/i,
    build: (m) => ({ math: `(${m[2]} - ${m[1]})/${m[1]} * 100`, goal: "evaluate", interpretation: `100 (${m[2]} - ${m[1]})/${m[1]} percent` }) },
  { id: "gcd", re: /^(?:find |what is |compute |calculate )?(?:the )?(?:gcd|gcf|hcf|greatest common (?:divisor|factor)|highest common factor) of (.+?)(?: and (.+))?$/i,
    build: (m) => ({ math: `gcd(${list(m[1], m[2])})`, goal: "evaluate", interpretation: `greatest common divisor of ${list(m[1], m[2])}` }) },
  { id: "lcm", re: /^(?:find |what is |compute |calculate )?(?:the )?(?:lcm|least common multiple|lowest common multiple) of (.+?)(?: and (.+))?$/i,
    build: (m) => ({ math: `lcm(${list(m[1], m[2])})`, goal: "evaluate", interpretation: `least common multiple of ${list(m[1], m[2])}` }) },
  { id: "prime-factor", re: /^(?:find |what is |what are |give )?(?:the )?(?:prime factori[sz]ation|prime factors|prime decomposition) of (\d+)$|^factori[sz]e (\d+)$/i,
    build: (m) => ({ math: `factorint(${m[1] || m[2]})`, goal: "evaluate", interpretation: `prime factorization of ${m[1] || m[2]}` }) },
  { id: "is-prime", re: /^is (\d+) (?:a )?prime(?: number)?(?: or (?:composite|not))?$/i,
    build: (m) => ({ math: `isprime(${m[1]})`, goal: "evaluate", interpretation: `is ${m[1]} prime` }) },
  { id: "divisors", re: /^(?:find |what are |list )?(?:all )?(?:the )?(?:positive )?(?:divisors|factors) of (\d+)$/i,
    build: (m) => ({ math: `divisors(${m[1]})`, goal: "evaluate", interpretation: `divisors of ${m[1]}` }) },
  { id: "remainder", re: /^(?:find |what is )?(?:the )?remainder (?:when|of) (.+?) (?:is )?divided by (.+)$/i,
    build: (m) => { const a = mathOf(m[1]), b = mathOf(m[2]); return a && b ? { math: `(${a}) mod (${b})`, goal: "evaluate", interpretation: `remainder of ${a} divided by ${b}` } : null; } },
  { id: "mean", re: /^(?:find |what is )?(?:the )?(mean|average|median|mode|variance|standard deviation) of (.+)$/i,
    build: (m) => { const f = { mean: "mean", average: "mean", median: "median", mode: "mode", variance: "variance", "standard deviation": "stdev" }[m[1].toLowerCase()];
      return { math: `${f}(${list(m[2])})`, goal: "evaluate", interpretation: `${m[1].toLowerCase()} of ${list(m[2])}` }; } },

  // ---- classic word problems (templates with explicit unknowns) ----
  { id: "number-plus", re: /^(?:a|some|the) number (?:plus|increased by|added to) (\S+) is (\S+)$/i,
    build: (m) => ({ math: `x + ${m[1]} = ${m[2]}`, goal: "solve", variable: "x", interpretation: `let x be the number: x + ${m[1]} = ${m[2]}` }) },
  { id: "number-minus", re: /^(?:a|some|the) number (?:minus|decreased by|less) (\S+) is (\S+)$/i,
    build: (m) => ({ math: `x - ${m[1]} = ${m[2]}`, goal: "solve", variable: "x", interpretation: `let x be the number: x - ${m[1]} = ${m[2]}` }) },
  { id: "k-times-number", re: /^(twice|double|triple|thrice|half|(\S+) times) (?:a|some|the) number (?:(plus|minus|increased by|decreased by) (\S+) )?(?:is|equals|gives) (\S+)$/i,
    build: (m) => { const k = MULT_WORDS[m[1].toLowerCase()] || m[2]; if (!/^[\d./]+$/.test(String(k)) && !mathOf(k)) return null; const op = m[3] ? (/plus|increased/i.test(m[3]) ? "+" : "-") : null;
      const lhs = `${paren(k)} x${op ? ` ${op} ${m[4]}` : ""}`;
      return { math: `${lhs} = ${m[5]}`, goal: "solve", variable: "x", interpretation: `let x be the number: ${lhs} = ${m[5]}` }; } },
  { id: "sum-difference", re: /^the sum of two numbers is (\S+) and their difference is (\S+)$/i,
    build: (m) => ({ math: `x + y = ${m[1]}, x - y = ${m[2]}`, goal: "solve", interpretation: `let the numbers be x >= y: x + y = ${m[1]}, x - y = ${m[2]}` }) },
  { id: "sum-product", re: /^the sum of two numbers is (\S+) and their product is (\S+)$/i,
    build: (m) => ({ math: `x + y = ${m[1]}, x*y = ${m[2]}`, goal: "solve", interpretation: `x + y = ${m[1]}, xy = ${m[2]}` }) },
  { id: "consecutive", re: /^the sum of (two|three|four|five|\d+) consecutive (even |odd )?(?:integers|numbers|whole numbers) is (\S+)$/i, build: (m) => consecutive(m[1], m[2], m[3]) },
  { id: "consecutive", re: /^(?:find )?(two|three|four|five|\d+) consecutive (even |odd )?(?:integers|numbers|whole numbers) (?:whose sum is|that add up to|with (?:a )?sum of|that sum to|add up to|sum to|have a sum of) (\S+)$/i,
    build: (m) => consecutive(m[1], m[2], m[3]) },
  // the numbers are computed unit-free; the unit of the answer is stated in the interpretation.
  // Mixed units (km with mph, minutes with km/h) are not converted here, so they are not matched.
  { id: "distance", re: /^(?:a|the) (?:car|train|bike|cyclist|runner|person|plane|boat|bus|truck) (?:travels|goes|drives|covers) (\S+?) ?(km|kilometers|kilometres|miles|m|mi|meters|metres) in (\S+?) ?(hours?|h|hrs?|minutes?|min|seconds?|s)(?:\.|,)? (?:what is|find) (?:its|the) (?:average )?speed$/i,
    build: (m) => { const d = unitOf(m[2], "len"), t = unitOf(m[4], "time"); if (!d || !t || !mathOf(m[1]) || !mathOf(m[3])) return null;
      return { math: `${m[1]}/${paren(m[3])}`, goal: "evaluate", interpretation: `speed = distance / time = ${m[1]} ${d} / ${m[3]} ${t}, in ${d}/${t}`, notes: [`The answer is in ${d}/${t}.`] }; } },
  { id: "distance", re: /^how long (?:does it take|will it take|would it take)(?: (?:a|the) (?:car|train|bike|runner|plane|boat|bus|truck))? to (?:travel|go|drive|cover) (\S+?) ?(km|kilometers|kilometres|miles|mi|m|meters|metres) at (\S+?) ?(km\/h|kph|kmh|mph|mi\/h|m\/s)$/i,
    build: (m) => { const d = unitOf(m[2], "len"), r = rateOf(m[4]); if (!d || !r || r[0] !== d || !mathOf(m[1]) || !mathOf(m[3])) return null;
      return { math: `${m[1]}/${paren(m[3])}`, goal: "evaluate", interpretation: `time = distance / speed = ${m[1]} ${d} / ${m[3]} ${m[4]}, in ${r[1]}`, notes: [`The answer is in ${r[1]}.`] }; } },
  { id: "distance", re: /^how far (?:does|will|would|can) (?:a|the) (?:car|train|bike|runner|person|plane|boat|bus|truck) (?:travel|go|drive) in (\S+?) ?(hours?|h|hrs?|minutes?|min|seconds?|s) at (\S+?) ?(km\/h|kph|kmh|mph|mi\/h|m\/s)$/i,
    build: (m) => { const t = unitOf(m[2], "time"), r = rateOf(m[4]); if (!t || !r || r[1] !== t || !mathOf(m[1]) || !mathOf(m[3])) return null;
      return { math: `${paren(m[1])}*${paren(m[3])}`, goal: "evaluate", interpretation: `distance = time * speed = ${m[1]} ${t} * ${m[3]} ${m[4]}, in ${r[0]}`, notes: [`The answer is in ${r[0]}.`] }; } },
  { id: "simple-interest", re: /^(?:what is |find |calculate )?(?:the )?simple interest (?:on|for) \$?(\S+) at (\S+) ?% (?:per year |a year |per annum |annually )?for (\S+) years?$/i,
    build: (m) => ({ math: `${m[1]} * ${m[2]}/100 * ${m[3]}`, goal: "evaluate", interpretation: `I = P r t = ${m[1]} * ${m[2]}% * ${m[3]}` }) },
  { id: "compound-interest", re: /^\$?(\S+) (?:is )?invested at (\S+) ?% (?:per year |a year |annually )?compounded (annually|monthly|quarterly|daily) for (\S+) years?(?:,|\.)? (?:what is|find) the (?:final )?(?:amount|balance|value)$/i,
    build: (m) => { const n = { annually: 1, monthly: 12, quarterly: 4, daily: 365 }[m[3].toLowerCase()];
      return { math: `${m[1]} (1 + ${m[2]}/(100*${n}))^(${n}*${m[4]})`, goal: "evaluate", interpretation: `A = P (1 + r/n)^(n t) with P = ${m[1]}, r = ${m[2]}%, n = ${n}, t = ${m[4]}` }; } },
  { id: "rectangle", re: /^(?:a|the) rectangle has (?:a )?perimeter (?:of )?(\S+) and (?:its )?length is (\S+) more than (?:its )?width(?:\.|,)? find (?:the|its) dimensions$/i,
    build: (m) => ({ math: `2(w + ${m[2]}) + 2w = ${m[1]}`, goal: "solve", variable: "w", interpretation: `width w, length w + ${m[2]}: 2(w + ${m[2]}) + 2w = ${m[1]}` }) },
  { id: "rectangle", re: /^(?:a|the) rectangle has (?:a )?length (?:of )?(\S+?),? and (?:a )?width (?:of )?(\S+?)(?:\.|,)? (?:what is|find) (?:its|the) (area|perimeter)$/i,
    build: (m) => { const L = mathOf(m[1]), W = mathOf(m[2]); if (!L || !W) return null; const area = /area/i.test(m[3]);
      return { math: area ? `${L}*${W}` : `2(${L} + ${W})`, goal: "evaluate", interpretation: area ? `area = length * width = ${L} * ${W}` : `perimeter = 2(length + width) = 2(${L} + ${W})` }; } },
  { id: "rectangle", re: /^the length of (?:a|the) rectangle is (twice|three times|(\S+) times|(\S+) (?:more|longer|less|shorter) than) its width,? and (?:its|the) (perimeter|area) is (\S+?)(?:\.|,)? find (?:the|its) (width|dimensions)$/i,
    build: (m) => {
      let L;
      if (/^twice$/i.test(m[1])) L = "2w"; else if (/^three times$/i.test(m[1])) L = "3w";
      else if (m[2]) { if (!mathOf(m[2])) return null; L = `${m[2]} w`; }
      else { if (!mathOf(m[3])) return null; L = /more|longer/i.test(m[1]) ? `w + ${m[3]}` : `w - ${m[3]}`; }
      const math = /perimeter/i.test(m[4]) ? `2(${L}) + 2w = ${m[5]}` : `(${L}) w = ${m[5]}`;
      return { math, goal: "solve", variable: "w", interpretation: `width w, length ${L}: ${math}` };
    } },
  { id: "age", re: /^(\w+) is (\S+) years older than (\w+)\. in (\S+) years,? (\w+) will be (twice|three times) as old as (\w+)\. how old is (\w+)(?: now)?$/i,
    build: (m) => { const k = /twice/i.test(m[6]) ? 2 : 3; const older = m[1], younger = m[3];
      if (m[8].toLowerCase() !== younger.toLowerCase()) return null;
      const eqn = m[5].toLowerCase() === older.toLowerCase() ? `(y + ${m[2]}) + ${m[4]} = ${k}(y + ${m[4]})` : `y + ${m[4]} = ${k}((y + ${m[2]}) + ${m[4]})`;
      return { math: eqn, goal: "solve", variable: "y", interpretation: `let y be ${younger}'s age now (${older} is y + ${m[2]}): ${eqn}` }; } },
  { id: "age", re: /^(\w+) is (twice|three times|four times|(\d+) times) as old as (?:her |his |their )?(\w+)\. the sum of their ages is (\d+)\. how old is (?:her |his |their )?(\w+)(?: now)?$/i,
    build: (m) => { const k = { twice: 2, "three times": 3, "four times": 4 }[m[2].toLowerCase()] || +m[3]; if (m[6].toLowerCase() !== m[4].toLowerCase()) return null;
      return { math: `${k}y + y = ${m[5]}`, goal: "solve", variable: "y", interpretation: `let y be the ${m[4]}'s age (${m[1]} is ${k}y): ${k}y + y = ${m[5]}` }; } },
  { id: "age", re: /^(\w+) is (\d+) years older than (\w+)\. the sum of their ages is (\d+)\. how old is (\w+)(?: now)?$/i,
    build: (m) => { if (m[5].toLowerCase() !== m[3].toLowerCase()) return null;
      return { math: `y + (y + ${m[2]}) = ${m[4]}`, goal: "solve", variable: "y", interpretation: `let y be ${m[3]}'s age (${m[1]} is y + ${m[2]}): y + (y + ${m[2]}) = ${m[4]}` }; } },
  { id: "mixture", re: /^how (?:many|much) (liters|litres|gallons|ml|milliliters|kg|grams|ounces|pounds|l) of (?:a |an )?(\d+(?:\.\d+)?) ?% (?:\w+ )?solution (?:must|should|do you need to|need to|has to) be (?:added to|mixed with) (\d+(?:\.\d+)?) (liters|litres|gallons|ml|milliliters|kg|grams|ounces|pounds|l) of (?:a |an )?(\d+(?:\.\d+)?) ?% (?:\w+ )?solution to (?:get|make|obtain|produce|give) (?:a |an )?(\d+(?:\.\d+)?) ?% (?:\w+ )?solution$/i,
    build: (m) => { if (m[1].toLowerCase() !== m[4].toLowerCase()) return null;
      // the target strength must lie strictly between the two, or the amount would be negative or undefined
      if (!(Math.min(+m[2], +m[5]) < +m[6] && +m[6] < Math.max(+m[2], +m[5]))) return null;
      const math = `${m[2]}/100 x + ${m[5]}/100*${m[3]} = ${m[6]}/100 (x + ${m[3]})`;
      return { math, goal: "solve", variable: "x", interpretation: `let x be the ${m[1]} of the ${m[2]}% solution: ${math}` }; } },

  // ---- generic verbs in front of math ----
  { id: "solve", re: /^(?:solve|find ([a-z]) (?:if|when|given|such that))(?: the (?:equation|inequality|inequalities|equations|differential equation))?:? (.+)$/i,
    build: (m) => ({ math: equationsText(m[2]), goal: "solve", variable: m[1], interpretation: `solve ${equationsText(m[2])}` }) },
  { id: "simplify", re: /^(?:fully |completely )?(simplify|expand|factor|factorise|factorize|reduce|rationali[sz]e)(?: and simplify)?(?: fully| completely)?(?: the (?:expression|fraction|polynomial))?:? (.+?)(?: fully| completely)?$/i,
    build: (m) => { let g = m[1].toLowerCase(); g = /^rationali/.test(g) ? "rationalize" : g.replace(/is[e]$|iz[e]$/, "").replace(/^factor.*/, "factor");
      const notes = [];
      if (g === "reduce") g = "simplify";
      if (/^rationali/.test(g)) { g = "simplify"; notes.push("Quelvra simplifies the expression; the result is equal but may still have a radical in the denominator."); }
      return { math: `${g}(${expr(m[2])})`, goal: g, interpretation: `${g} ${expr(m[2])}`, notes }; } },
  { id: "evaluate", re: /^(?:what is|what's|whats|calculate|compute|evaluate|find the value of|find|how much is|work out|give me|determine)(?: the value of)? (.+)$/i, build: (m) => ({ math: expr(m[1]), goal: "evaluate", interpretation: expr(m[1]) }) },
  { id: "plot", re: /^(?:plot|graph|draw|sketch) (?:the graph of )?(.+)$/i, build: (m) => ({ math: expr(m[1]), goal: "plot", interpretation: `graph of ${expr(m[1])}` }) },
];

function deriv(f, v, ord) {
  const names = ["", "", "second ", "third ", "fourth ", "fifth "];
  return { math: ord === 1 ? `d/d${v} (${f})` : `d^${ord}/d${v}^${ord} (${f})`, goal: "differentiate", variable: v, pattern: "derivative", interpretation: `${names[ord] || ""}derivative of ${f} with respect to ${v}` };
}
function integralOf(body, v0, lo, hi) {
  let s = String(body).trim(), v = v0, m;
  if ((m = s.match(/^(.+?)\s*\bd([a-z])$/))) { s = m[1]; if (v && v !== m[2]) return null; v = m[2]; }
  const fx = fnOf(s);
  if (!fx) return null;
  v = v || fx.x;
  if (lo !== undefined && lo !== null) {
    const a = bound(lo), b = bound(hi);
    if (!a || !b) return null;
    return { math: `integrate(${fx.f}, ${v}, ${a}, ${b})`, goal: "integrate", variable: v, interpretation: `integral of ${fx.f} from ${a} to ${b}` };
  }
  return { math: `integrate(${fx.f}, ${v})`, goal: "integrate", variable: v, interpretation: `antiderivative of ${fx.f} with respect to ${v}` };
}
function limitOf(body, v, to0, side0) {
  const side = side0 ? (/(right|above)/i.test(side0) ? "^+" : "^-") : "";
  let t = String(to0).trim(), s2 = "";
  const m = t.match(/^(.+?)(\+|-|\^\+|\^-)$/);
  if (m && !side) { t = m[1]; s2 = m[2].replace(/^(?!\^)/, "^"); }
  const to = /infinity/i.test(t) ? (/negative|minus|-/i.test(t) ? "-oo" : "oo") : mathOf(t);
  const f = mathOf(body);
  if (!to || !f) return null;
  const sd = side || s2;
  return { math: `lim_(${v}->${to}${sd}) (${f})`, goal: "limit", variable: v, pattern: "limit", interpretation: `limit of ${f} as ${v} -> ${to}${sd ? (sd === "^+" ? " from the right" : " from the left") : ""}` };
}
function bigOp(kind, body, v, lo, hi) {
  const f = mathOf(body), a = bound(lo), b = bound(hi);
  if (!f || !a || !b) return null;
  const op = /sum/i.test(kind) ? "sum" : "prod";
  return { math: `${op}(${f}, ${v}, ${a}, ${b})`, goal: op === "sum" ? "sum" : "product", variable: v, interpretation: `${op === "sum" ? "sum" : "product"} of ${f} for ${v} from ${a} to ${b}` };
}
function points(cmd, [a, b, c, d]) {
  const v = [a, b, c, d].map(mathOf);
  if (v.some((t) => !t)) return null;
  return { math: `${cmd}(${v.join(", ")})`, goal: cmd, interpretation: `${cmd} for the points (${v[0]}, ${v[1]}) and (${v[2]}, ${v[3]})` };
}
function identityOf(s) {
  const t = expr(s);
  const m = t.match(/^([^=<>!]+)=([^=<>]+)$/);
  if (!m) return null;
  const l = m[1].trim(), r = m[2].trim();
  if (!looksLikeMath(l) || !looksLikeMath(r)) return null;
  return { math: `identity(${l}, ${r})`, goal: "identity", interpretation: `is ${l} = ${r} true for every value of the variables` };
}
function seriesOf(s0, maclaurin, taylor) {
  let s = s0.trim(), n = null, a = null, m;
  const notes = [];
  if ((m = s.match(/^(.+?),?\s+(?:(?:up )?to|through|of)?\s*(?:the )?(?:order|degree)\s+(\d+)$/i)) || (m = s.match(/^(.+?),?\s+(?:up )?to (?:the )?(?:x\^(\d+)|(\d+)(?:st|nd|rd|th) (?:order|degree|power))$/i))) {
    s = m[1]; n = m[2] || m[3];
  }
  if ((m = s.match(/^(.+?),?\s+(?:at|about|around|centered at|centred at|near|expanded at|expanded about) (?:the point )?(?:[a-z] ?= ?)?(.+)$/i))) { s = m[1]; a = bound(m[2]); if (!a) return null; }
  if (maclaurin) { if (a && a !== "0") return null; a = "0"; }
  if (!a) { a = "0"; notes.push("Expanded about 0 (no centre was given)."); }
  if (!n) { n = "5"; notes.push("Order 5 (no order was given)."); }
  const fx = fnOf(s);
  if (!fx) return null;
  const cmd = taylor ? "taylor" : "series";
  return { math: `${cmd}(${fx.f}, ${fx.x}, ${a}, ${n})`, goal: cmd, variable: fx.x, interpretation: `${taylor ? "Taylor polynomial" : "series expansion"} of ${fx.f} about ${fx.x} = ${a} to order ${n}`, notes };
}
function consecutive(count, parity, total) {
  const n = +wordsToNumbers(count);
  if (!(n >= 2 && n <= 10)) return null;
  const step = parity ? 2 : 1;
  const terms = Array.from({ length: n }, (_, i) => (i ? `(n + ${i * step})` : "n")).join(" + ");
  return { math: `${terms} = ${total}`, goal: "solve", variable: "n", interpretation: `let n be the smallest: ${terms} = ${total}`, notes: ["Check that n is an integer" + (parity ? ` and ${parity.trim()}` : "") + "."] };
}

// polite framing around a request: "please", "can you", "hey quelvra," ... "for me"
const PREFIX = /^(?:please|kindly|can you|could you|would you|will you|help me(?: to)?|i need to|i want to|i'd like to|i would like to|let's|lets|let us|hey quelvra|hi quelvra|hello quelvra|quelvra|hey|now|ok|okay)[,:]?\s+/i;
const SUFFIX = /\s+(?:for me|please|thanks|thank you)$/i;

// "log of 100" (English, no base named) is read as base 10: say so
function logNote(math, words, notes) {
  if (/\blog\b(?!_)/.test(math) && /\blog(?:arithm)?\b(?! base)/i.test(words) && !/natural log/i.test(words)) notes.push("log without a base is read as log base 10; say natural log (ln) otherwise.");
  return notes;
}

// Notation that the parser would misread: nCr / nPr shorthands, "n choose k", P(Z < a) for the
// standard normal, "a mod m" inverses. Rewritten to function calls before anything else.
const NUM = String.raw`-?\d+(?:\.\d+)?`;
const NOTATION = [
  [re(String.raw`^(.*?)\b(\d+|[a-z])\s+choose\s+(\d+|[a-z])\b(.*)$`), (m) => `${m[1]}binomial(${m[2]}, ${m[3]})${m[4]}`],
  [/\bC\(\s*(\d+)\s*,\s*(\d+)\s*\)/g, (m) => `binomial(${m[1]}, ${m[2]})`],
  [/\bP\(\s*(\d+)\s*,\s*(\d+)\s*\)/g, (m) => `nPr(${m[1]}, ${m[2]})`],
  [/\b(\d+)\s*C\s*(\d+)\b/g, (m) => `binomial(${m[1]}, ${m[2]})`],
  [/\b(\d+)\s*P\s*(\d+)\b/g, (m) => `nPr(${m[1]}, ${m[2]})`],
  [re(String.raw`\bP\(\s*Z\s*(<=?|≤)\s*(${NUM})\s*\)`, "g"), (m) => `normalcdf(-oo, ${m[2]})`],
  [re(String.raw`\bP\(\s*Z\s*(>=?|≥)\s*(${NUM})\s*\)`, "g"), (m) => `normalcdf(${m[2]}, oo)`],
  [re(String.raw`\bP\(\s*(${NUM})\s*(?:<=?|≤)\s*Z\s*(?:<=?|≤)\s*(${NUM})\s*\)`, "g"), (m) => `normalcdf(${m[1]}, ${m[2]})`],
];
function notation(s) {
  for (const [rx, f] of NOTATION) {
    if (rx.global) s = s.replace(rx, (...a) => f(a));
    else { const m = s.match(rx); if (m) s = f(m); }
  }
  return s;
}

// Main entry.
// advanced discrete commands (engine/discrete/lang.js): graphs, logic, sets, permutations, finite
// fields, LP, games, cryptography, homology and proof requests become canonical call forms
import { translateAdvancedDiscrete } from "./discrete/lang.js";
export function translate(input) {
  const advDiscrete = translateAdvancedDiscrete(String(input || ""));
  if (advDiscrete) return advDiscrete;
  let raw = clean(notation(String(input || "").replace(/\s+/g, " ")));
  // "2+2=" / "2+2 = ?": an evaluation request
  if (/=\s*$/.test(raw) && (raw.match(/=/g) || []).length === 1 && !/[<>]/.test(raw)) raw = clean(raw.replace(/=\s*$/, ""));
  if (!raw) return { ok: false, reason: "empty input" };
  // Already math: nothing to translate.
  if (looksLikeMath(raw)) {
    if (raw !== String(input).trim()) return { ok: true, math: raw, goal: null, interpretation: raw, pattern: "math-clean", confidence: 1, notes: [] };
    return { ok: true, math: raw, goal: null, interpretation: raw, pattern: "math", confidence: 1, notes: [] };
  }
  let lower = raw;
  for (let k = 0; k < 4; k++) { const t = lower.replace(PREFIX, "").replace(SUFFIX, ""); if (t === lower) break; lower = clean(t); }
  if (!lower) return { ok: false, reason: "empty input" };
  lower = clean(lower.replace(TAIL, ""));
  if (lower !== raw && looksLikeMath(lower)) return { ok: true, math: lower, goal: null, interpretation: lower, pattern: "math-polite", confidence: 0.95, notes: [] };
  let firstFail = null;
  for (const p of PATTERNS) {
    const m = lower.match(p.re);
    if (!m) continue;
    const r = p.build(m);
    // a pattern that understood the problem and found it impossible stops here instead of letting a looser pattern guess
    if (r && r.refuse) return { ok: false, reason: r.refuse, pattern: p.id };
    if (!r || !r.math) continue;
    if (!looksLikeMath(r.math)) {
      firstFail = firstFail || { ok: false, reason: `Understood the request as "${p.id}", but part of it is not recognisable math: "${r.math}". Please rewrite it using symbols.`, pattern: p.id };
      continue;
    }
    const pattern = r.pattern || p.id;
    const notes = [...(r.notes || [])];
    logNote(r.math, lower, notes);
    return { ok: true, confidence: pattern === "evaluate" || pattern === "solve" ? 0.9 : 0.95, ...r, pattern, notes };
  }
  if (firstFail) return firstFail;
  // last resort: word-to-symbol translation only if the result is pure math
  const t = expr(lower);
  if (looksLikeMath(t)) return { ok: true, math: t, goal: null, interpretation: t, pattern: "phrases", confidence: 0.75, notes: logNote(t, lower, ["Translated word by word; check the interpretation."]) };
  return { ok: false, reason: "This sentence did not match any problem pattern Quelvra knows, so it will not guess. Try writing the equation directly, for example: 2x + 3 = 11." };
}
