// Word problems for the language engine: ages, mixtures, work and rates, distance-speed-time,
// percentages, interest, consecutive integers, measurement, simple probability, unit rates,
// ratios, "a number" sentences, two-unknown systems (tickets, coins, heads and legs) and angles.
//
// Like language.js this module only TRANSLATES: it turns a whole problem into equations (or a
// formula) and says in `interpretation` which unknowns and which model it used; the engine then
// solves and verifies. The rules that keep it honest:
//   - every sentence of the problem must be understood; one unknown sentence refuses the problem
//     (skipping a sentence could drop a fact and give a wrong answer);
//   - the arithmetic sentences ("five more than twice a number") go through a small grammar that
//     enumerates every reading; two readings with different meanings refuse;
//   - templates are anchored to the whole sentence and to explicit structure (units, "as old as",
//     "per hour"); a keyword alone never decides the model;
//   - preconditions that the model needs (consecutive integers really are integers of the right
//     parity, units agree, a probability question names a listed colour) are checked before the
//     translation is returned, otherwise the problem is refused.

// ---------------------------------------------------------------- normalisation
const NUMBER = String.raw`\d+(?:\.\d+)?`;
const Q = String.raw`(\d+(?:\.\d+)?|\(\d+\/\d+\))`; // a captured quantity
import { parse } from "./parse.js";
import { evalReal } from "./verify.js";

const NAME_STOP = new Set(["he", "she", "it", "they", "him", "her", "them", "his", "their", "its", "sum", "ratio", "age", "ages", "product", "difference", "total", "number", "in", "the", "a", "an", "and", "years", "year"]);
const FORBIDDEN_VARS = new Set(["e", "i", "d", "o", "l"]);
const PARITY = { even: 2, odd: 2 };
const num = (s) => { const m = /^\((\d+)\/(\d+)\)$/.exec(String(s)); return m ? Number(m[1]) / Number(m[2]) : Number(s); };
const fmt = (s) => String(s).replace(/^\((\d+)\/(\d+)\)$/, "($1/$2)");
// numbers as math text: fractions keep their parentheses
const M = (x) => (typeof x === "number" ? (Number.isInteger(x) ? String(x) : String(x)) : fmt(x));

export function normaliseWords(s, wordsToNumbers) {
  let t = String(s).replace(/[’‘`]/g, "'").replace(/[“”]/g, '"').replace(/\s+/g, " ").trim();
  t = t.replace(/(\d),(?=\d{3}\b)/g, "$1");
  t = t.replace(/\$\s*(\d+(?:\.\d+)?)/g, "$1 dollars");
  t = t.replace(/(\d)\s*°/g, "$1 degrees");
  t = t.toLowerCase();
  // "the larger one", "each one", "which one": the pronoun, not the number
  t = t.replace(/\b(larger|smaller|largest|smallest|greater|greatest|bigger|biggest|other|first|second|third|middle|last|each|which|every|this|that) one\b/g, "$1 \u0001");
  t = wordsToNumbers(t).replace(/\u0001/g, "one");
  // "20 %" / "20 percent" -> "20%"
  t = t.replace(/(\d)\s*(?:%|percent\b|per cent\b)/g, "$1%");
  t = t.replace(/\bdollars dollars\b/g, "dollars").replace(/(\d) dollars (?:dollars|usd)\b/g, "$1 dollars");
  t = t.replace(/(\d+)-(hour|minute|day|ounce|pound|liter|litre|gallon|mile|year|sided)s?\b/g, "$1 $2");
  t = t.replace(/\s+([,;:])/g, "$1").replace(/\s+/g, " ").trim();
  return t;
}
// sentences, without their final punctuation
export function sentencesOf(t) {
  return t.split(/(?<=[.?!;])\s+/).map((x) => x.replace(/[.?!;,]+$/, "").trim()).filter(Boolean);
}

// ---------------------------------------------------------------- the arithmetic grammar
// sum  := prod (op prod)*  |  prod ("more than" | "less than" ...) sum
// prod := unary (("times" | "multiplied by" | "divided by") unary)*
// unary:= twice/double/triple/half of/(k/n) of/p% of/the square of/... unary | atom [squared|cubed]
// atom := number | noun | the sum/difference/product/quotient of sum and sum
// Every reading is kept; the caller refuses when two complete readings mean different things.
const node = (s, f, p, j) => ({ s, f, p, j });
const wrap = (n, min) => (n.p < min ? `(${n.s})` : n.s);
const isNumTok = (t) => /^\d+(?:\.\d+)?$/.test(t) || /^\(\d+\/\d+\)$/.test(t);
function mulText(a, b) {
  if (a.p >= 3 && /^\d+(?:\.\d+)?$/.test(a.s) && /^[a-z]$/.test(b.s)) return `${a.s}${b.s}`;
  if (a.p >= 3 && /^\(\d+\/\d+\)$/.test(a.s) && /^[a-z]$/.test(b.s)) return `${a.s} ${b.s}`;
  return `${wrap(a, 2)}*${wrap(b, 3)}`;
}
const OPS_ADD = [[["plus"], "+"], [["increased", "by"], "+"], [["added", "to"], "+"], [["+"], "+"], [["minus"], "-"], [["decreased", "by"], "-"], [["reduced", "by"], "-"], [["diminished", "by"], "-"], [["-"], "-"], [["subtracted", "from"], "-r"]];
const OPS_MUL = [[["times"], "*"], [["multiplied", "by"], "*"], [["divided", "by"], "/"], [["*"], "*"], [["/"], "/"]];
const MORE = [[["more", "than"], "+"], [["greater", "than"], "+"], [["larger", "than"], "+"], [["less", "than"], "-"], [["fewer", "than"], "-"], [["smaller", "than"], "-"]];
const PREFIX_K = { twice: 2, double: 2, triple: 3, thrice: 3, quadruple: 4 };
const FRACTION_OF = { half: 2, third: 3, quarter: 4, fourth: 4, fifth: 5, tenth: 10 };

function makeGrammar(tokens, nouns) {
  const memo = new Map();
  const at = (i, words) => words.every((w, k) => tokens[i + k] === w);
  const cache = (key, fn) => { if (!memo.has(key)) { memo.set(key, []); memo.set(key, fn()); } return memo.get(key); };
  function atom(i) {
    return cache(`a${i}`, () => {
      const out = [];
      const t = tokens[i];
      if (t === undefined) return out;
      if (isNumTok(t)) out.push(node(t, () => num(t), 3, i + 1));
      for (const nn of nouns) if (at(i, nn.words)) out.push(node(nn.s, nn.f, nn.p || 3, i + nn.words.length));
      const binary = [[["the", "sum", "of"], (a, b) => node(`${a.s} + ${b.s}`, (v) => a.f(v) + b.f(v), 1)], [["the", "total", "of"], (a, b) => node(`${a.s} + ${b.s}`, (v) => a.f(v) + b.f(v), 1)],
        [["the", "difference", "between"], (a, b) => node(`${a.s} - ${wrap(b, 2)}`, (v) => a.f(v) - b.f(v), 1)], [["the", "difference", "of"], (a, b) => node(`${a.s} - ${wrap(b, 2)}`, (v) => a.f(v) - b.f(v), 1)],
        [["the", "product", "of"], (a, b) => node(mulText(a, b), (v) => a.f(v) * b.f(v), 2)], [["the", "quotient", "of"], (a, b) => node(`${wrap(a, 2)}/${wrap(b, 3)}`, (v) => a.f(v) / b.f(v), 2)]];
      for (const [w, mk] of binary) {
        if (!at(i, w)) continue;
        for (const a of sum(i + w.length)) {
          if (tokens[a.j] !== "and") continue;
          for (const b of sum(a.j + 1)) { const n = mk(a, b); n.j = b.j; n.p = 3; n.s = `(${n.s})`; out.push(n); }
        }
      }
      return out;
    });
  }
  function unary(i) {
    return cache(`u${i}`, () => {
      const out = [];
      const t = tokens[i];
      if (t === undefined) return out;
      if (PREFIX_K[t]) for (const u of unary(i + 1)) out.push(node(mulText(node(String(PREFIX_K[t]), null, 3), u), (v) => PREFIX_K[t] * u.f(v), 2, u.j));
      // half of x, a third of x, one quarter of x, (2/3) of x, 20% of x
      let k = i, den = null, coef = null, ctext = null;
      if ((tokens[k] === "a" || tokens[k] === "one" || tokens[k] === "1") && FRACTION_OF[tokens[k + 1]]) { den = FRACTION_OF[tokens[k + 1]]; k += 2; }
      else if (tokens[k] === "half") { den = 2; k += 1; }
      else if (/^\(\d+\/\d+\)$/.test(tokens[k] || "") && tokens[k + 1] === "of") { coef = num(tokens[k]); ctext = tokens[k]; k += 1; }
      else if (/^\d+(?:\.\d+)?%$/.test(tokens[k] || "") && tokens[k + 1] === "of") { coef = Number(tokens[k].slice(0, -1)) / 100; ctext = `(${tokens[k].slice(0, -1)}/100)`; k += 1; }
      if ((den || coef !== null) && tokens[k] === "of") {
        for (const u of unary(k + 1)) {
          if (den) out.push(node(`${wrap(u, 2)}/${den}`, (v) => u.f(v) / den, 2, u.j));
          else out.push(node(`${ctext}*${wrap(u, 3)}`, (v) => coef * u.f(v), 2, u.j));
        }
      } else if (tokens[i] === "half" && tokens[k] !== "of") {
        for (const u of unary(k)) out.push(node(`${wrap(u, 2)}/2`, (v) => u.f(v) / 2, 2, u.j)); // "half the number"
      }
      if (at(i, ["the", "square", "of"])) for (const u of unary(i + 3)) out.push(node(`${wrap(u, 3)}^2`, (v) => u.f(v) ** 2, 3, u.j));
      if (at(i, ["the", "cube", "of"])) for (const u of unary(i + 3)) out.push(node(`${wrap(u, 3)}^3`, (v) => u.f(v) ** 3, 3, u.j));
      if (at(i, ["the", "reciprocal", "of"])) for (const u of unary(i + 3)) out.push(node(`1/${wrap(u, 3)}`, (v) => 1 / u.f(v), 2, u.j));
      for (const a of atom(i)) {
        out.push(a);
        if (tokens[a.j] === "squared") out.push(node(`${wrap(a, 4)}^2`, (v) => a.f(v) ** 2, 3, a.j + 1));
        if (tokens[a.j] === "cubed") out.push(node(`${wrap(a, 4)}^3`, (v) => a.f(v) ** 3, 3, a.j + 1));
      }
      return out;
    });
  }
  function chain(first, ops, next, combine) {
    const all = [...first];
    let frontier = first;
    for (let guard = 0; frontier.length && guard < 12; guard++) {
      const nx = [];
      for (const r of frontier) for (const [w, op] of ops) {
        if (!at(r.j, w)) continue;
        for (const q of next(r.j + w.length)) { const c = combine(r, q, op); c.j = q.j; nx.push(c); }
      }
      all.push(...nx);
      frontier = nx;
    }
    return all;
  }
  function prod(i) {
    return cache(`p${i}`, () => chain(unary(i), OPS_MUL, unary, (a, b, op) => (op === "*" ? node(mulText(a, b), (v) => a.f(v) * b.f(v), 2) : node(`${wrap(a, 2)}/${wrap(b, 3)}`, (v) => a.f(v) / b.f(v), 2))));
  }
  function sum(i) {
    return cache(`s${i}`, () => {
      const out = chain(prod(i), OPS_ADD, prod, (a, b, op) => (op === "+" ? node(`${a.s} + ${b.s}`, (v) => a.f(v) + b.f(v), 1)
        : op === "-" ? node(`${a.s} - ${wrap(b, 2)}`, (v) => a.f(v) - b.f(v), 1) : node(`${b.s} - ${wrap(a, 2)}`, (v) => b.f(v) - a.f(v), 1)));
      for (const a of prod(i)) for (const [w, op] of MORE) {
        if (!at(a.j, w)) continue;
        for (const b of sum(a.j + w.length)) out.push(op === "+" ? node(`${b.s} + ${a.s}`, (v) => b.f(v) + a.f(v), 1, b.j) : node(`${b.s} - ${wrap(a, 2)}`, (v) => b.f(v) - a.f(v), 1, b.j));
      }
      return out;
    });
  }
  return { sum, tokens };
}
const tokenize = (s) => String(s).replace(/,/g, " ").replace(/\s+/g, " ").trim().split(" ").filter(Boolean);
// the value of a reading at a few points, for comparing readings
const PTS = [{ x: 1.37, y: -2.29, z: 0.61 }, { x: 2.91, y: 0.83, z: -1.7 }, { x: -0.73, y: 3.17, z: 2.3 }];
function sample(f, vars) {
  return PTS.map((p, k) => { const env = {}; vars.forEach((v, n) => { env[v] = [p.x, p.y, p.z][(n + k) % 3] + n * 0.37; }); try { return f(env); } catch (_) { return NaN; } });
}
const sameVals = (a, b) => a.every((x, k) => (Number.isNaN(x) && Number.isNaN(b[k])) || Math.abs(x - b[k]) <= 1e-9 * Math.max(1, Math.abs(x)));
// every complete reading of the phrase; null when there is none or two differ in meaning
export function readPhrase(s, nouns, vars) {
  const toks = tokenize(s);
  if (!toks.length) return null;
  const g = makeGrammar(toks, nouns);
  const full = g.sum(0).filter((n) => n.j === toks.length);
  if (!full.length) return null;
  const v0 = sample(full[0].f, vars);
  if (full.some((n) => !sameVals(sample(n.f, vars), v0))) return { ambiguous: true };
  return full[0];
}
// "LHS is RHS": tries every "is"/"equals" split; exactly one meaning must survive
const EQ_WORDS = [["is", "equal", "to"], ["is", "the", "same", "as"], ["equals"], ["is"], ["gives"], ["=",], ["will", "be"], ["was"], ["makes"], ["results", "in"]];
export function readEquation(s, nouns, vars) {
  const toks = tokenize(s);
  const found = [];
  for (let i = 1; i < toks.length - 1; i++) {
    for (const w of EQ_WORDS) {
      if (!w.every((x, k) => toks[i + k] === x)) continue;
      const l = readPhrase(toks.slice(0, i).join(" "), nouns, vars), r = readPhrase(toks.slice(i + w.length).join(" "), nouns, vars);
      if (!l || !r) continue;
      if (l.ambiguous || r.ambiguous) return { ambiguous: true };
      found.push({ l, r, f: (v) => l.f(v) - r.f(v) });
    }
  }
  if (!found.length) return null;
  const v0 = sample(found[0].f, vars);
  // "a b = c" and "a = b c" split differently only if the words allow two meanings
  if (found.some((e) => !sameVals(sample(e.f, vars), v0))) return { ambiguous: true };
  return { text: `${found[0].l.s} = ${found[0].r.s}`, f: found[0].f };
}
// noun table entry: words of the noun phrase -> variable
const noun = (phrase, v, f) => ({ words: phrase.split(" "), s: v, f: f || ((env) => env[v]) });

// real roots of a polynomial (degree <= 2) given as a function, found from its values
function polyRoots(f) {
  const f0 = f(0), f1 = f(1), fm = f(-1), f2 = f(2);
  const a = (f1 + fm) / 2 - f0, b = (f1 - fm) / 2, c = f0;
  // degree check: the quadratic through three points must reproduce the fourth
  if (Math.abs(a * 4 + b * 2 + c - f2) > 1e-7 * Math.max(1, Math.abs(f2))) return null;
  if (Math.abs(a) < 1e-12) return Math.abs(b) < 1e-12 ? null : [-c / b];
  const D = b * b - 4 * a * c;
  if (D < -1e-12) return [];
  const r = Math.sqrt(Math.max(0, D));
  return D < 1e-12 ? [-b / (2 * a)] : [(-b - r) / (2 * a), (-b + r) / (2 * a)];
}
const isInt = (x) => Math.abs(x - Math.round(x)) < 1e-9;
// Solve the equations of a translation ("x + y = 20, 2x + 4y = 56") when they are linear with one solution.
// Used only to check that the solution makes sense for the story (no negative counts, ages or angles);
// the engine still solves and verifies the equations itself. Returns { x: value, ... } or null.
function linearSolution(math, vars) {
  let fs;
  try {
    fs = math.split(", ").filter((e) => / = /.test(e) && !/[<>]/.test(e)).map((e) => {
      const [l, r] = e.split(" = ").map((t) => parse(t));
      return (env) => evalReal(l, env) - evalReal(r, env);
    });
  } catch (_) { return null; }
  const n = vars.length;
  if (fs.length !== n) return null;
  const env = (vals) => Object.fromEntries(vars.map((v, k) => [v, vals[k]]));
  const zero = vars.map(() => 0);
  const A = [], b = [];
  for (const f of fs) {
    const c = f(env(zero));
    const row = vars.map((_, k) => f(env(vars.map((_, j) => (j === k ? 1 : 0)))) - c);
    // linear: a second point must agree
    const pt = vars.map((_, k) => 1.7 + 0.9 * k);
    const pred = c + row.reduce((s2, a, k) => s2 + a * pt[k], 0);
    if (![c, ...row].every(Number.isFinite) || Math.abs(f(env(pt)) - pred) > 1e-7 * Math.max(1, Math.abs(pred))) return null;
    A.push(row); b.push(-c);
  }
  // Gaussian elimination with partial pivoting
  for (let col = 0; col < n; col++) {
    let piv = col;
    for (let r = col + 1; r < n; r++) if (Math.abs(A[r][col]) > Math.abs(A[piv][col])) piv = r;
    if (Math.abs(A[piv][col]) < 1e-12) return null;
    [A[col], A[piv]] = [A[piv], A[col]]; [b[col], b[piv]] = [b[piv], b[col]];
    for (let r = 0; r < n; r++) {
      if (r === col) continue;
      const k = A[r][col] / A[col][col];
      for (let c2 = col; c2 < n; c2++) A[r][c2] -= k * A[col][c2];
      b[r] -= k * b[col];
    }
  }
  return Object.fromEntries(vars.map((v, k) => [v, b[k] / A[k][k]]));
}
// every value passes the test (counts, ages and angles must make sense), else refuse
const sensible = (math, vars, okv) => { const sol = linearSolution(math, vars); return !!sol && vars.every((v) => okv(sol[v], v)); };
const COUNT = (x) => x >= -1e-9 && isInt(x);

// ---------------------------------------------------------------- helpers for results
// "(a + b) = 41" -> "a + b = 41": drop brackets that wrap a whole side
function bareSides(eq) {
  return eq.split(" = ").map((side) => {
    if (!/^\(.*\)$/.test(side)) return side;
    let depth = 0;
    for (let k = 0; k < side.length; k++) {
      depth += side[k] === "(" ? 1 : side[k] === ")" ? -1 : 0;
      if (depth === 0 && k < side.length - 1) return side; // "(a)(b)": the first bracket closes early
    }
    return side.slice(1, -1);
  }).join(" = ");
}
const tidy = (t) => t.split(", ").map(bareSides).join(", ");
// understood, but the story has no sensible answer: translate() reports this instead of trying other patterns
const impossible = (why) => ({ refuse: `This reads as a word problem, but it has no sensible answer: ${why}.` });
function result(pattern, math, interpretation, extra = {}) {
  return { math: tidy(math), interpretation: interpretation.split(": ").map((x, k) => (k ? tidy(x) : x)).join(": "), goal: "solve", pattern, notes: [], ...extra };
}
const QUESTION_NUMBER = /^(?:so )?(?:find|what is|what's|determine|calculate|work out|solve for|give) (?:the|this|that) (?:unknown )?number$|^(?:find|what is) it$|^what (?:is|was) the (?:original )?number$|^what number is (?:it|this)$|^find the value of the number$/;

// ---------------------------------------------------------------- "a number" sentences
const X_NOUNS = ["a number", "the number", "some number", "a certain number", "an unknown number", "the unknown number", "this number", "that number", "a number x", "the number x", "x", "n"].map((p) => noun(p, /x$/.test(p) || p === "x" ? "x" : p === "n" ? "n" : "x"));
function numberSentence(sents) {
  if (!sents.length) return null;
  let body = sents[0];
  const rest = sents.slice(1);
  if (!rest.every((q) => QUESTION_NUMBER.test(q))) return null;
  body = body.replace(/^(?:find|what is) (?:a|the) number (?:such that|if|so that|where|when) /, "");
  if (/\bn\b/.test(body) && /\bx\b/.test(body)) return null;
  const v = /\bn\b/.test(body) && !/\bx\b/.test(body) ? "n" : "x";
  const nouns = X_NOUNS.filter((n) => n.s === v || n.words.length > 1).map((n) => ({ ...n, s: v, f: (env) => env[v] }));
  // "when/if A is added to B, the result is C"
  let m, eq;
  const RESULT = String.raw`,? (?:the result is|the answer is|the sum is|you get|we get|it gives|the result will be|it equals|the total is)`;
  if ((m = new RegExp(String.raw`^(?:when|if) (.+?) is (added to|subtracted from|multiplied by|divided by|increased by|decreased by) (.+?)${RESULT} (.+)$`).exec(body))) {
    const op = m[2];
    const phrase = op === "added to" ? `${m[3]} plus ${m[1]}` : op === "subtracted from" ? `${m[3]} minus ${m[1]}` : `${m[1]} ${op} ${m[3]}`;
    eq = readEquation(`${phrase} is ${m[4]}`, nouns, [v]);
  } else if ((m = new RegExp(String.raw`^(?:when|if) (.+?) is (doubled|tripled|halved|squared)${RESULT} (.+)$`).exec(body))) {
    const phrase = m[2] === "doubled" ? `twice ${m[1]}` : m[2] === "tripled" ? `triple ${m[1]}` : m[2] === "halved" ? `half of ${m[1]}` : `${m[1]} squared`;
    eq = readEquation(`${phrase} is ${m[3]}`, nouns, [v]);
  } else eq = readEquation(body, nouns, [v]);
  if (!eq || eq.ambiguous) return null;
  if (!new RegExp(`(?<![a-z])${v}(?![a-z])`).test(eq.text)) return null;
  return result("word-number", eq.text, `let ${v} be the number: ${eq.text}`, { variable: v });
}

// ---------------------------------------------------------------- two unknown numbers
function twoNumbers(sents) {
  const text = sents.join(". ");
  if (!/\b(?:two|2) (?:positive )?numbers\b|\b(?:1|one) number\b.*\b(?:another|the other)\b/.test(text)) return null;
  if (/\bconsecutive\b|\bthree\b|\b3 numbers\b/.test(text)) return null;
  // roles: larger/smaller, first/second or one/other; mixing them refuses
  const sizeRole = /\b(?:larger|smaller|greater|bigger|lesser)\b/.test(text), ordRole = /\b(?:first|second)\b/.test(text);
  if (sizeRole && ordRole) return null;
  const X_ = sizeRole ? ["the larger number", "the larger", "the greater number", "the greater", "the bigger number", "the bigger", "(?:one|1) number"] : ordRole ? ["the first number", "the first"] : ["(?:one|1) number", "one of the numbers", "1 of the numbers", "(?:one|1) of them"];
  const Y_ = sizeRole ? ["the smaller number", "the smaller", "the lesser number", "the lesser", "the other number", "the other", "another number", "another"] : ordRole ? ["the second number", "the second"] : ["the other number", "the other", "another number", "another", "the other one"];
  const nouns = [];
  for (const p of X_) for (const w of p.includes("(?:one|1)") ? [p.replace("(?:one|1)", "one"), p.replace("(?:one|1)", "1")] : [p]) nouns.push(noun(w, "x"));
  for (const p of Y_) nouns.push(noun(p, "y"));
  nouns.sort((a, b) => b.words.length - a.words.length);
  const eqs = [];
  let asked = null;
  for (const s0 of sents) {
    const s = s0.replace(/^(?:and )/, "");
    let m;
    if (/^(?:find|what are|determine|give) (?:the|both|these|those)? ?(?:2 |two )?numbers$|^what are they$|^find them$/.test(s)) { asked = "both"; continue; }
    if ((m = /^(?:find|what is|determine) the (larger|smaller|greater|lesser|bigger|first|second) (?:number|one)?$/.exec(s))) { asked = /larg|great|bigg|first/.test(m[1]) ? "x" : "y"; continue; }
    const parts = s.split(/,? and (?=their |the (?:sum|difference|product)|(?:one|1) |the (?:larger|smaller|first|second|other))/);
    for (const p0 of parts) {
      const p = p0.replace(/^(?:the )?sum of (?:the |these )?(?:two |2 )?(?:positive )?numbers\b/, "their sum").replace(/^(?:the )?(difference|product) (?:of|between) (?:the |these )?(?:two |2 )?(?:positive )?numbers\b/, "their $1")
        .replace(/^(?:two|2) (?:positive )?numbers (?:add up to|have a sum of|sum to|total) /, "their sum is ").replace(/^(?:two|2) (?:positive )?numbers have a (sum|difference|product) of /, "their $1 is ");
      if ((m = new RegExp(`^their sum is ${Q}$`).exec(p))) { eqs.push(`x + y = ${M(m[1])}`); continue; }
      if ((m = new RegExp(`^their difference is ${Q}$`).exec(p))) { eqs.push(`x - y = ${M(m[1])}`); continue; }
      if ((m = new RegExp(`^their product is ${Q}$`).exec(p))) { eqs.push(`x*y = ${M(m[1])}`); continue; }
      if ((m = /^(?:the )?(?:two |2 )?numbers are in the ratio (\d+) ?(?::|to) ?(\d+)$/.exec(p))) { eqs.push(`${m[2]}x = ${m[1]}y`); continue; }
      const e = readEquation(p, nouns, ["x", "y"]);
      if (!e || e.ambiguous) return null;
      eqs.push(e.text);
    }
  }
  if (eqs.length !== 2) return null;
  const who = sizeRole ? "x the larger number, y the smaller" : ordRole ? "x the first number, y the second" : "x one number, y the other";
  return result("word-two-numbers", eqs.join(", "), `let ${who}: ${eqs.join(", ")}${asked === "x" || asked === "y" ? ` (the question asks for ${asked})` : ""}`);
}

// ---------------------------------------------------------------- consecutive integers
const CONSEC = String.raw`(2|3|4|5|6) consecutive (positive |negative )?(even |odd )?(?:positive )?(?:integers|numbers|whole numbers|natural numbers)`;
function consecutiveInts(sents) {
  const text = sents.join(". ");
  const m0 = new RegExp(CONSEC).exec(text);
  if (!m0) return null;
  const n = +m0[1], sign = (m0[2] || "").trim(), par = (m0[3] || "").trim(), step = par ? 2 : 1;
  // every mention must describe the same list
  for (const mm of text.matchAll(new RegExp(CONSEC, "g"))) if (mm[0] !== m0[0]) return null;
  const names = ["a", "b", "c", "f", "g", "h"].slice(0, n);
  const term = (k) => (k === 0 ? "a" : `a + ${k * step}`);
  const f = (k) => (env) => env.a + k * step;
  const nouns = [];
  const last = n - 1;
  const add = (ps, k) => { for (const p of ps) nouns.push({ words: p.split(" "), s: names[k], f: (env) => env[names[k]] }); };
  add(["the smallest", "the smaller", "the first", "the least", "the lesser", "the smallest integer", "the smaller integer", "the first integer", "the smallest number", "the smaller number", "the first number", "the smallest one", "the smaller one", "the first one"], 0);
  add(["the largest", "the larger", "the greatest", "the biggest", "the last", "the largest integer", "the larger integer", "the greatest integer", "the largest number", "the larger number", "the greatest number", "the last integer", "the last number", "the largest one", "the larger one"], last);
  if (n >= 3) add(["the second", "the second integer", "the second number"], 1);
  if (n === 3) add(["the middle", "the middle integer", "the middle number", "the middle one"], 1);
  if (n >= 4) add(["the third", "the third integer", "the third number"], 2);
  const sumS = names.join(" + "), sumF = (env) => names.reduce((t, v) => t + env[v], 0);
  for (const p of ["their sum", "the sum of the integers", "the sum of the numbers", "the sum of these integers", "the sum of the 2 integers", "the sum of the 3 integers", "the sum"]) nouns.push({ words: p.split(" "), s: `(${sumS})`, f: sumF, p: 3 });
  if (n === 2) for (const p of ["their product", "the product of the integers", "the product of the numbers"]) nouns.push({ words: p.split(" "), s: `${names[0]}*${names[1]}`, f: (env) => env.a * env.b, p: 2 });
  nouns.sort((a, b) => b.words.length - a.words.length);
  const eqs = [];
  let asked = null;
  const L = m0[0];
  for (const s0 of sents) {
    let s = s0, m;
    if (/^(?:find|what are|determine|list|name) (?:the|these|those|all)? ?(?:integers|numbers|them|the \d+ integers|the \d+ numbers)$|^what are (?:they|the integers|the numbers)$/.test(s)) { asked = "all"; continue; }
    if ((m = /^(?:find|what is|determine|name) the (smallest|smaller|first|least|largest|larger|greatest|biggest|last|middle|second|third)(?: integer| number| one)?(?: of (?:them|these|the integers|the numbers))?$/.exec(s))) { asked = m[1]; continue; }
    // "find 3 consecutive integers whose sum is 72" / "3 consecutive integers add up to 72"
    s = s.replace(new RegExp(`^(?:find |there are )?${escape(L)} (?:whose|with a|that have a|having a|which have a) (sum|product) (?:is |of )?`), "the $1 of them is ")
      .replace(new RegExp(`^(?:find )?${escape(L)} (?:that |which )?(?:add up to|sum to|have a sum of|total) `), "the sum of them is ")
      .replace(new RegExp(`^the (sum|product) of ${escape(L)}`), "the $1 of them")
      .replace(new RegExp(`^(twice |3 times |thrice )?the (smallest|smaller|largest|larger|first|second|greatest|middle) of ${escape(L)}`), "$1the $2")
      .replace(/^the sum of them\b/, "their sum").replace(/^the product of them\b/, "their product");
    if (new RegExp(escape(L)).test(s)) return null;
    // "... is 72, find the integers" handled as separate sentences only
    const e = readEquation(s, nouns, names);
    if (!e || e.ambiguous) return null;
    eqs.push(e);
  }
  if (!eqs.length) return null;
  // reduce to one equation in a (the smallest): every name is a + k*step
  if (eqs.length !== 1) return null;
  const g = (a) => { const env = {}; names.forEach((v, k) => { env[v] = a + k * step; }); return eqs[0].f(env); };
  const roots = polyRoots(g);
  if (!roots || !roots.length) return null;
  const keep = roots.filter((r) => (sign === "positive" ? r > 0 : sign === "negative" ? r + (n - 1) * step < 0 : true));
  if (!keep.length) return null;
  for (const r of keep) {
    if (!isInt(r)) return null;
    if (par === "even" && Math.round(r) % 2 !== 0) return null;
    if (par === "odd" && Math.abs(Math.round(r) % 2) !== 1) return null;
  }
  if (keep.length !== roots.length && roots.length > 1) {
    // a sign word removes one root: one variable with a condition keeps the answer exact and checked
    const single = eqs[0].text.replace(/\b([bcfgh])\b/g, (v) => `(${term(names.indexOf(v))})`);
    return result("word-consecutive", `${single}, a ${sign === "positive" ? ">" : "<"} 0`, `let a be the smallest of ${n} consecutive ${par ? par + " " : ""}integers (${names.map((v, k) => (k ? `${v} = ${term(k)}` : "a")).join(", ")}): ${single}, with a ${sign}`, { variable: "a" });
  }
  const defs = names.slice(1).map((v, k) => `${v} = ${term(k + 1)}`);
  const math = [eqs[0].text, ...defs].join(", ");
  return result("word-consecutive", math, `${n} consecutive ${par ? par + " " : ""}integers a${names.slice(1).map((v, k) => `, ${v} = ${term(k + 1)}`).join("")}: ${eqs[0].text}${asked && asked !== "all" ? ` (the question asks for the ${asked})` : ""}`);
}
function escape(s) { return s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&"); }

// ---------------------------------------------------------------- ages
const NM = String.raw`((?:(?:a|an|the|her|his|their|my|your) )?[a-z]+(?: [a-z]+)?)`;
const K_TIMES = String.raw`(twice|thrice|half|(\d+(?:\.\d+)?) times)`;
const kOf = (w, d) => (w === "twice" ? 2 : w === "thrice" ? 3 : w === "half" ? "1/2" : d);
const AGE_ROLES = new Set(["father", "mother", "son", "daughter", "brother", "sister", "grandfather", "grandmother", "uncle", "aunt", "cousin", "friend", "wife", "husband", "dad", "mom", "mum", "child", "boy", "girl", "man", "woman", "teacher", "student", "grandson", "granddaughter", "nephew", "niece", "baby", "dog", "cat"]);
function ages(sents) {
  const text = sents.join(". ");
  if (!/\b(?:old|older|younger|age|ages|years ago|in \d+ years)\b/.test(text)) return null;
  const ent = new Map(); // key -> letter
  let lastSubject = null, target = null, targetAdd = 0;
  const used = new Set();
  const letterFor = (key) => {
    if (ent.has(key)) return ent.get(key);
    let v = key[0];
    if (!/[a-z]/.test(v) || used.has(v) || FORBIDDEN_VARS.has(v)) v = [..."xyzuvwpqrstabcfghjkmn"].find((c) => !used.has(c));
    used.add(v); ent.set(key, v);
    return v;
  };
  const who = (raw, subject = true) => {
    let k = String(raw).trim().replace(/^(?:a|an|the|her|his|their|my|your) /, "").replace(/'s$/, "");
    if (/^(?:he|she|him)$/.test(k)) { if (!lastSubject) return null; return lastSubject; }
    if (NAME_STOP.has(k) || /\d/.test(k)) return null;
    if (k.includes(" ")) {
      const [a, b] = k.split(" ");
      if (NAME_STOP.has(a) || NAME_STOP.has(b)) return null;
      if (AGE_ROLES.has(b)) k = b; // "the eldest son" style is not read: only the role word is kept
      else if (AGE_ROLES.has(a)) k = b; // "her brother tom": the name is the entity
      else return null;
    } // "her older brother" is refused above; "the eldest son" style is not read
    if (!AGE_ROLES.has(k) && !/^[a-z]{2,}$/.test(k)) return null;
    const v = letterFor(k);
    if (subject) lastSubject = k;
    return k;
  };
  const eqs = [];
  const V = (k) => ent.get(k);
  for (const s0 of sents) {
    const s = s0.replace(/^and /, "").replace(/ now$| today$| currently$/, "").replace(/ (?:is|are) now /, " is ").replace(/, /g, " ");
    let m, a, b;
    // questions
    if ((m = new RegExp(`^(?:so )?how old (?:is|was) ${NM}(?: now| today)?$`).exec(s)) || (m = new RegExp(`^(?:what is|find|determine) ${NM}'s (?:present |current )?age(?: now)?$`).exec(s))) {
      const k = who(m[1], false); if (!k || !ent.has(k)) return null; target = k; continue;
    }
    if ((m = new RegExp(`^how old will ${NM} be in (\\d+) years$`).exec(s))) { const k = who(m[1], false); if (!k || !ent.has(k)) return null; target = k; targetAdd = +m[2]; continue; }
    if (/^how old are (?:they|both of them|the two)(?: now)?$|^(?:find|what are) their (?:present |current )?ages$/.test(s)) { target = "all"; continue; }
    // facts
    if ((m = new RegExp(`^${NM} is (\\d+(?:\\.\\d+)?) years? (older|younger) than ${NM}(?: is)?$`).exec(s))) {
      if (!(a = who(m[1])) || !(b = who(m[4], false)) || a === b) return null; eqs.push(`${V(a)} = ${V(b)} ${m[3] === "older" ? "+" : "-"} ${m[2]}`); lastSubject = a; continue;
    }
    if ((m = new RegExp(`^${NM} is ${K_TIMES} as old as ${NM}(?: is)?$`).exec(s)) || (m = new RegExp(`^${NM} is ${K_TIMES} (?:the age of ${NM}|${NM}'s age)$`).exec(s))) {
      const other = m[4] || m[5];
      if (!(a = who(m[1])) || !(b = who(other, false)) || a === b) return null; eqs.push(`${V(a)} = ${M(kOf(m[2], m[3]))}${V(b)}`.replace(/= 1\/2(\w)/, "= $1/2")); lastSubject = a; continue;
    }
    if ((m = new RegExp(`^in (\\d+) years ${NM} will be ${K_TIMES} as old as ${NM}(?: will be)?$`).exec(s))) {
      if (!(a = who(m[2])) || !(b = who(m[5], false)) || a === b) return null; const k = kOf(m[3], m[4]); eqs.push(`${V(a)} + ${m[1]} = ${k === "1/2" ? `(${V(b)} + ${m[1]})/2` : `${k}(${V(b)} + ${m[1]})`}`); lastSubject = a; continue;
    }
    if ((m = new RegExp(`^(\\d+) years ago ${NM} was ${K_TIMES} as old as ${NM}(?: was)?$`).exec(s))) {
      if (!(a = who(m[2])) || !(b = who(m[5], false)) || a === b) return null; const k = kOf(m[3], m[4]); eqs.push(`${V(a)} - ${m[1]} = ${k === "1/2" ? `(${V(b)} - ${m[1]})/2` : `${k}(${V(b)} - ${m[1]})`}`); lastSubject = a; continue;
    }
    if ((m = new RegExp(`^in (\\d+) years ${NM} will be (\\d+)(?: years old)?$`).exec(s))) { if (!(a = who(m[2]))) return null; eqs.push(`${V(a)} + ${m[1]} = ${m[3]}`); continue; }
    if ((m = new RegExp(`^(\\d+) years ago ${NM} was (\\d+)(?: years old)?$`).exec(s))) { if (!(a = who(m[2]))) return null; eqs.push(`${V(a)} - ${m[1]} = ${m[3]}`); continue; }
    if ((m = new RegExp(`^${NM} is (\\d+)(?: years old| years of age)?$`).exec(s)) || (m = new RegExp(`^${NM}'s age is (\\d+)(?: years)?$`).exec(s))) { if (!(a = who(m[1]))) return null; eqs.push(`${V(a)} = ${m[2]}`); continue; }
    if ((m = new RegExp(`^the ratio of ${NM}'s age to ${NM}'s age is (\\d+) ?(?::|to) ?(\\d+)$`).exec(s))) {
      if (!(a = who(m[1])) || !(b = who(m[2], false)) || a === b) return null; eqs.push(`${m[4]}${V(a)} = ${m[3]}${V(b)}`); continue;
    }
    // sums of ages of exactly two people
    const pair = () => { const ks = [...ent.keys()]; return ks.length === 2 ? ks : null; };
    if ((m = new RegExp(`^the sum of the ages of ${NM} and ${NM} is (\\d+)$`).exec(s))) {
      if (!(a = who(m[1])) || !(b = who(m[2], false)) || a === b) return null; eqs.push(`${V(a)} + ${V(b)} = ${m[3]}`); continue;
    }
    if ((m = /^(?:the sum of their (?:present )?ages|their (?:present )?ages add up to|their combined age|the total of their ages|together their ages total|their ages total) (?:is |are )?(\d+)(?: years)?$/.exec(s))) {
      const p = pair(); if (!p) return null; eqs.push(`${V(p[0])} + ${V(p[1])} = ${m[1]}`); continue;
    }
    if ((m = /^in (\d+) years the sum of their ages will be (\d+)$/.exec(s))) { const p = pair(); if (!p) return null; eqs.push(`(${V(p[0])} + ${m[1]}) + (${V(p[1])} + ${m[1]}) = ${m[2]}`); continue; }
    if ((m = /^(\d+) years ago the sum of their ages was (\d+)$/.exec(s))) { const p = pair(); if (!p) return null; eqs.push(`(${V(p[0])} - ${m[1]}) + (${V(p[1])} - ${m[1]}) = ${m[2]}`); continue; }
    // "Peter's age is 5 more than twice Paul's age": the arithmetic grammar with the ages as nouns
    if ((m = /^([a-z]+)'s age is (.+)$/.exec(s))) {
      for (const mm of s.matchAll(/\b([a-z]+)'s age\b/g)) if (!who(mm[1], false)) return null;
      const nouns = [];
      for (const [k, v] of ent) for (const p of [`${k}'s age`, `${k}'s present age`, `${k}'s current age`]) nouns.push(noun(p, v));
      nouns.sort((x, y) => y.words.length - x.words.length);
      const e = readEquation(s, nouns, [...ent.values()]);
      if (!e || e.ambiguous) return null;
      lastSubject = m[1];
      eqs.push(e.text); continue;
    }
    return null; // a sentence that was not understood
  }
  if (!target || !eqs.length || eqs.length !== ent.size) return null;
  {
    // ages now, and ages "k years ago", cannot be negative
    const letters = [...ent.values()];
    const sol = linearSolution(eqs.join(", "), letters);
    if (sol) {
      if (letters.some((v) => !(sol[v] >= 0))) return impossible("someone's age would be negative");
      for (const m2 of eqs.join(" ").matchAll(/\b([a-z]) - (\d+(?:\.\d+)?)\b/g)) if (sol[m2[1]] !== undefined && sol[m2[1]] - +m2[2] < -1e-9) return impossible("someone's age in the past would be negative");
    }
  }
  const vars = [...ent.entries()].map(([k, v]) => `${v} = ${AGE_ROLES.has(k) ? `the ${k}` : k[0].toUpperCase() + k.slice(1)}'s age now`).join(", ");
  if (targetAdd) {
    const w = [..."tuvwpqrs"].find((c) => !used.has(c));
    const all = [...eqs, `${w} = ${V(target)} + ${targetAdd}`];
    return result("word-age", all.join(", "), `let ${vars}; ${w} = ${target}'s age in ${targetAdd} years: ${all.join(", ")}`);
  }
  return result("word-age", eqs.join(", "), `let ${vars}: ${eqs.join(", ")}${target !== "all" ? ` (the question asks for ${V(target)})` : ""}`, eqs.length === 1 ? { variable: V(target) } : {});
}

export const _internal = { readPhrase, readEquation, noun, polyRoots, normaliseWords, sentencesOf };
export { numberSentence, twoNumbers, consecutiveInts, ages };
export { geometry, boxVolume, probability, unitRates, ratios, systems, angles };


// ---------------------------------------------------------------- clause consumption
// A sentence is understood only when a sequence of known clauses covers all of it.
const JOIN = /^(?:,\s*|\s+)(?:and\s+|but\s+|so\s+|then\s+|while\s+)?/;
function consume(s, clauses, st) {
  let rest = s.trim(), first = true;
  while (rest) {
    if (!first) { const c = JOIN.exec(rest); if (!c || !c[0]) return false; rest = rest.slice(c[0].length); if (!rest) return false; }
    let hit = false;
    for (const [re, act] of clauses) {
      const m = re.exec(rest);
      if (!m || !m[0]) continue;
      if (act(m, st) === false) return false;
      rest = rest.slice(m[0].length);
      hit = true;
      break;
    }
    if (!hit) return false;
    first = false;
  }
  return true;
}
const C = (src) => new RegExp(`^(?:${src})(?=,|\\s|$)`);
const N = String.raw`(\d+(?:\.\d+)?)`;
const sing = (w) => String(w).replace(/ies$/, "y").replace(/(ch|sh|x|ss)es$/, "$1").replace(/(?<!s)s$/, "");
const set1 = (st, k, v) => { if (st[k] !== undefined && st[k] !== v) return false; st[k] = v; return true; };
// questions are whole sentences; every other sentence must be consumed by the clauses
function runFacts(sents, clauses, questions, st) {
  for (const s of sents) {
    let q = false;
    for (const [re, act] of questions) { const m = re.exec(s); if (m) { if (act(m, st) === false) return false; q = true; break; } }
    if (q) continue;
    // "..., what is X": a trailing question after a comma
    const k = s.search(/,? (?:what|how|find) /);
    if (k > 0) {
      const head = s.slice(0, k), tail = s.slice(k).replace(/^,? /, "");
      let hit = false;
      for (const [re, act] of questions) { const m = re.exec(tail); if (m) { if (act(m, st) === false) return false; hit = true; break; } }
      if (hit) { if (!consume(head.replace(/^if /, ""), clauses, st)) return false; continue; }
    }
    if (!consume(s.replace(/^if /, ""), clauses, st)) return false;
  }
  return true;
}

// ---------------------------------------------------------------- mixtures
const MU = String.raw`(liters?|litres?|gallons?|quarts?|ml|milliliters?|millilitres?|kg|kilograms?|grams?|ounces?|oz|pounds?|lbs?|cups?|pints?|tons?|l)`;
const unitKey = (u) => ({ l: "liter", litre: "liter", litres: "liter", lb: "pound", lbs: "pound", kilogram: "kg", kilograms: "kg", milliliter: "ml", millilitre: "ml", milliliters: "ml", millilitres: "ml", oz: "ounce" }[u] || sing(u));
const PCT = String.raw`(?:a |an )?(\d+(?:\.\d+)?)% (?:([a-z]+) )?(?:solution|mixture|alloy|brine)(?: of ([a-z]+))?`;
function mixtures(sents) {
  const text = sents.join(". ");
  let m;
  const same = (a, b) => unitKey(a) === unitKey(b);
  const subst = (a, b) => !a || !b || a === b; // the substances named must agree
  const ADD = String.raw`(?:must|should|do you need to|does one need to|needs to|need to|has to|have to|will need to|would need to|can) be (?:added to|mixed with|combined with)`;
  const GET = String.raw`to (?:get|make|obtain|produce|give|form|yield|create|end up with|result in)`;
  const one = sents.length === 1 ? sents[0] : null;
  if (one) {
    // how many liters of a 20% solution must be added to 10 liters of a 50% solution to get a 30% solution
    const WHAT = String.raw`(?:${PCT}|(pure water|distilled water|water)|pure ([a-z]+))`;
    if ((m = new RegExp(`^how (?:many|much) (?:${MU} (?:of )?)?${WHAT} ${ADD} ${N} ${MU} (?:of )?${PCT} ${GET} ${PCT}$`).exec(one))) {
      const [, u1, p, s1, s1b, water, pure, V, u2, q, s2, s2b, r, s3, s3b] = m;
      if (u1 && !same(u1, u2)) return null;
      const sub2 = s2 || s2b, sub3 = s3 || s3b;
      if (!subst(sub2, sub3) || !subst(s1 || s1b, sub2) || (pure && !subst(pure, sub2))) return null;
      const P = water ? 0 : pure ? 100 : +p;
      // the target must lie strictly between the two strengths, or no positive amount works
      if (!(Math.min(P, +q) < +r && +r < Math.max(P, +q))) return impossible(`a ${r}% mixture cannot be made from ${P}% and ${q}%`);
      const lhs = P === 0 ? `${q}*${V}` : `${P === 100 ? "100x" : `${P}x`} + ${q}*${V}`;
      const math = `${lhs} = ${r}(x + ${V})`;
      return result("word-mixture", math, `let x be the ${unitKey(u2)}s of ${water ? "water (0%)" : pure ? `pure ${pure} (100%)` : `the ${P}% solution`} added; amount of pure substance, in percent units: ${math}`, { variable: "x" });
    }
    // how much water must be evaporated from 50 liters of a 10% solution to make a 25% solution
    if ((m = new RegExp(`^how (?:many|much) (?:${MU} (?:of )?)?water (?:must|should|needs to|has to|will need to) be (?:evaporated|removed|boiled off|boiled away) from ${N} ${MU} (?:of )?${PCT} ${GET}(?: it)? ${PCT}$`).exec(one))) {
      const [, u1, V, u2, q, s2, s2b, r, s3, s3b] = m;
      if ((u1 && !same(u1, u2)) || !subst(s2 || s2b, s3 || s3b) || !(+r > +q && +r <= 100)) return null;
      const math = `${q}*${V} = ${r}(${V} - x)`;
      return result("word-mixture", math, `let x be the ${unitKey(u2)}s of water removed; the dissolved amount stays the same: ${math}`, { variable: "x" });
    }
    // how many gallons of a 30% solution and a 60% solution must be mixed to obtain 12 gallons of a 50% solution
    if ((m = new RegExp(`^how (?:many|much) ${MU} (?:of )?(?:each of )?${PCT} and ${PCT} (?:must|should|are needed to|need to|have to|will need to) (?:be )?(?:mixed|combined|used) ${GET} ${N} ${MU} (?:of )?${PCT}$`).exec(one))) {
      const [, u1, p, , , q, , , T, u2, r] = m;
      if (!same(u1, u2) || !(Math.min(+p, +q) < +r && +r < Math.max(+p, +q))) return null;
      const math = `x + y = ${T}, ${p}x + ${q}y = ${r}*${T}`;
      return result("word-mixture", math, `let x = ${unitKey(u1)}s of the ${p}% solution, y = ${unitKey(u1)}s of the ${q}% solution: ${math}`);
    }
  }
  // two sentences: A is mixed with B to get T of C. how many of A (each) ...
  const MIXV = String.raw`(?:(?:a|the) \w+ )?(?:mixes|combines|mixed|combined|(?:is|are) mixed|(?:is|are) combined)`;
  if (sents.length === 2) {
    const [a, b] = sents;
    if ((m = new RegExp(`^(?:a |the )?(?:\\w+ )?${MIXV} ${PCT} (?:with|and) ${PCT} ${GET} ${N} ${MU} (?:of )?${PCT}$`).exec(a))) {
      const [, p, , , q, , , T, u, r] = m;
      if (!(Math.min(+p, +q) < +r && +r < Math.max(+p, +q))) return null;
      let want = null, mm;
      if ((mm = new RegExp(`^how (?:many|much) ${MU} of the ${N}% (?:\\w+ )?(?:solution )?(?:are|is|were|was|should be|must be|will be) (?:used|needed|required)$`).exec(b))) { if (!same(mm[1], u)) return null; want = mm[2] === p ? "x" : mm[2] === q ? "y" : null; if (!want) return null; }
      else if ((mm = new RegExp(`^how (?:many|much) ${MU} of each (?:solution )?(?:are|is|were|should be|must be) (?:used|needed|required)$`).exec(b))) { if (!same(mm[1], u)) return null; want = "both"; }
      else return null;
      const math = `x + y = ${T}, ${p}x + ${q}y = ${r}*${T}`;
      return result("word-mixture", math, `let x = ${unitKey(u)}s of the ${p}% solution, y = ${unitKey(u)}s of the ${q}% solution: ${math}${want !== "both" ? ` (the question asks for ${want})` : ""}`);
    }
    // a 60 liter mixture is 30% juice. how much juice must be added to make it 50% juice
    // a farmer has 100 liters of milk that is 4% butterfat. how much cream that is 20% butterfat should be added to get milk that is 6% butterfat
    let V, u, q, sub;
    if ((m = new RegExp(`^(?:a|an|the) ${N} ${MU} (?:mixture|solution|batch|tank|container) (?:is|contains) ${N}% ([a-z]+)$`).exec(a))) [, V, u, q, sub] = m;
    else if ((m = new RegExp(`^(?:(?:a|an|the) [a-z]+ (?:has|had|mixes|makes) |there (?:is|are) )?${N} ${MU} of (?:a )?(?:[a-z]+) (?:that is|which is|that contains|which contains|containing) ${N}% ([a-z]+)$`).exec(a))) [, V, u, q, sub] = m;
    if (V) {
      let mm;
      const TO = String.raw`to (?:make|get|obtain|produce|give)(?: it| the mixture| the solution| a mixture that is| a solution that is| (?:[a-z]+) that is)?`;
      if ((mm = new RegExp(`^how (?:many|much) (?:${MU} of )?(?:pure )?([a-z]+) (?:must|should|needs to|has to|will need to) be added(?: to it)? ${TO} ${N}% ([a-z]+)$`).exec(b))) {
        const [, u2, what, r, sub2] = mm;
        if ((u2 && !same(u2, u)) || what !== sub || sub2 !== sub || !(+r > +q && +r < 100)) return null;
        const math = `${q}*${V} + 100x = ${r}(${V} + x)`;
        return result("word-mixture", math, `let x be the ${unitKey(u)}s of pure ${sub} added: ${math}`, { variable: "x" });
      }
      if ((mm = new RegExp(`^how (?:many|much) (?:${MU} of )?([a-z]+) (?:that is|which is|containing) ${N}% ([a-z]+) (?:must|should|needs to|has to|will need to) be added(?: to it)? ${TO} ${N}% ([a-z]+)$`).exec(b))) {
        const [, u2, , p, sub1, r, sub2] = mm;
        if ((u2 && !same(u2, u)) || sub1 !== sub || sub2 !== sub || !(Math.min(+p, +q) < +r && +r < Math.max(+p, +q))) return null;
        const math = `${q}*${V} + ${p}x = ${r}(${V} + x)`;
        return result("word-mixture", math, `let x be the ${unitKey(u)}s of the ${p}% ${sub} added: ${math}`, { variable: "x" });
      }
    }
  }
  // price mixtures: coffee worth $6 per pound mixed with coffee worth $10 per pound ...
  const PR = String.raw`(?:worth|costing|that costs?|which costs?|selling for|that sells for|priced at|valued at|at) ${N} dollars (?:per|a|an|each) ${MU}`;
  const ITEM = String.raw`([a-z]+(?: [a-z]+)?)`;
  if (sents.length === 2) {
    const [a, b] = sents;
    // (1) both amounts unknown, total known in the first sentence
    if ((m = new RegExp(`^${ITEM} ${PR} (?:is|are) (?:mixed|combined|blended) with ${ITEM} ${PR} to (?:make|get|produce|obtain|form) ${N} ${MU}(?: of (?:a )?(?:mixture|blend))? ${PR}$`).exec(a))) {
      const [, i1, p, u1, i2, q, u2, T, u, r, u3] = m;
      if (![u1, u2, u3].every((x) => same(x, u)) || !(Math.min(+p, +q) < +r && +r < Math.max(+p, +q)) || sing(i1) !== sing(i2)) return null;
      let mm, want;
      if ((mm = new RegExp(`^how (?:many|much) ${MU} of the ${N} dollars? (?:[a-z]+ )?(?:are|is|were|was|should be|must be|will be) (?:used|needed|required)$`).exec(b))) { if (!same(mm[1], u)) return null; want = mm[2] === p ? "x" : mm[2] === q ? "y" : null; if (!want) return null; }
      else if ((mm = new RegExp(`^how (?:many|much) ${MU} of each (?:are|is|were|should be|must be) (?:used|needed|required)$`).exec(b))) { if (!same(mm[1], u)) return null; want = "both"; }
      else return null;
      const math = `x + y = ${T}, ${p}x + ${q}y = ${r}*${T}`;
      return result("word-mixture", math, `let x = ${unitKey(u)}s at ${p} dollars, y = ${unitKey(u)}s at ${q} dollars; the total value is unchanged: ${math}${want !== "both" ? ` (the question asks for ${want})` : ""}`);
    }
    // (2) prices first, then "how many of each are needed to make T of a mixture costing r"
    if ((m = new RegExp(`^${ITEM} ${PR} (?:is|are) (?:mixed|combined|blended) with ${ITEM} ${PR}$`).exec(a))) {
      const [, i1, p, u1, i2, q, u2] = m;
      let mm;
      if (!(mm = new RegExp(`^how (?:many|much) ${MU} of each (?:are|is|should be|must be|will be) (?:used|needed|required) to (?:make|get|produce|obtain) ${N} ${MU} of (?:a )?(?:mixture|blend) ${PR}$`).exec(b))) return null;
      const [, u, T, uT, r, ur] = mm;
      if (![u1, u2, uT, ur].every((x) => same(x, u)) || sing(i1) !== sing(i2) || !(Math.min(+p, +q) < +r && +r < Math.max(+p, +q))) return null;
      const math = `x + y = ${T}, ${p}x + ${q}y = ${r}*${T}`;
      return result("word-mixture", math, `let x = ${unitKey(u)}s at ${p} dollars, y = ${unitKey(u)}s at ${q} dollars: ${math}`);
    }
    // (3) one amount known: A worth p is mixed with V of B worth q. how many of A to make a mixture worth r
    if ((m = new RegExp(`^${ITEM} ${PR} (?:is|are) (?:mixed|combined|blended) with ${N} ${MU} of ${ITEM} ${PR}$`).exec(a))) {
      const [, i1, p, u1, V, u, i2, q, u2] = m;
      let mm;
      if (!(mm = new RegExp(`^how (?:many|much) ${MU} of the ${N} dollars? (?:[a-z]+ )?(?:are|is|should be|must be|will be) (?:used|needed|required|added) to (?:make|get|produce|obtain) (?:a )?(?:mixture|blend) ${PR}$`).exec(b))) return null;
      const [, uq, pq, r, ur] = mm;
      if (![u1, u2, uq, ur].every((x) => same(x, u)) || pq !== p || sing(i1) !== sing(i2) || !(Math.min(+p, +q) < +r && +r < Math.max(+p, +q))) return null;
      const math = `${p}x + ${q}*${V} = ${r}(x + ${V})`;
      return result("word-mixture", math, `let x be the ${unitKey(u)}s at ${p} dollars: value before = value after, ${math}`, { variable: "x" });
    }
  }
  return null;
}

// ---------------------------------------------------------------- work and rates
const TU = String.raw`(hours?|hrs?|minutes?|mins?|days?|weeks?|seconds?)`;
const tKey = (u) => ({ hr: "hour", hrs: "hour", min: "minute", mins: "minute" }[u] || sing(u));
const WORKERS = String.raw`(workers|people|men|women|machines|painters|builders|pumps|robots|printers|students|farmers|laborers|labourers|employees|cooks|typists|masons|carpenters|gardeners|computers)`;
const NEG_VERB = /^(?:empty|empties|drain|drains|leak|leaks)\b/;
function work(sents) {
  let m;
  const text = sents.join(". ");
  // inverse proportion: N1 workers take T1; how long for N2 workers (same job)
  {
    let n1, w1, t1, u1, mm;
    if ((m = new RegExp(`^(?:if )?${N} ${WORKERS} can (?:[a-z]+ ){1,6}?in ${N} ${TU}$`).exec(sents[0])) || (m = new RegExp(`^(?:if )?${N} ${WORKERS} (?:take|need) ${N} ${TU} to (?:[a-z]+ ?){1,6}$`).exec(sents[0])) || (m = new RegExp(`^it takes ${N} ${WORKERS} ${N} ${TU} to (?:[a-z]+ ?){1,6}$`).exec(sents[0]))) [, n1, w1, t1, u1] = m;
    let q = sents[1];
    if (!n1 && sents.length === 1 && (mm = new RegExp(`^(?:if )?(${N} ${WORKERS} can (?:[a-z]+ ){1,6}?in ${N} ${TU}),? (how .+)$`).exec(sents[0]))) { [, , n1, w1, t1, u1] = mm; q = mm[6]; }
    if (n1 && q && sents.length <= 2) {
      if ((mm = new RegExp(`^how (?:long|many ${TU}) (?:will|would|does|do|should) (?:it take )?${N} ${WORKERS}(?: take)?(?: to (?:[a-z]+ ?){1,6})?(?: working at the same rate)?$`).exec(q))) {
        const [, u2, n2, w2] = mm;
        if (w2 !== w1 || (u2 && tKey(u2) !== tKey(u1))) return null;
        const math = `${n1}*${t1} = ${n2}t`;
        return result("word-work", math, `the job needs ${n1} x ${t1} ${w1}-${tKey(u1)}s; with ${n2} ${w1} it takes t ${tKey(u1)}s: ${math}`, { variable: "t", notes: ["Assumes every worker works at the same steady rate."] });
      }
      return null;
    }
  }
  // machines x time -> items: if 6 machines can make 300 parts in 5 hours, how many parts can 9 machines make in 5 hours
  if (sents.length === 1 && (m = new RegExp(`^if ${N} ${WORKERS} (?:can )?([a-z]+) ${N} ([a-z]+) in ${N} ${TU},? how many ([a-z]+) (?:can|will|would|do) ${N} ([a-z]+) ([a-z]+) in ${N} ${TU}$`).exec(sents[0]))) {
    const [, n1, w1, v1, a1, it1, t1, u1, it2, n2, w2, v2, t2, u2] = m;
    if (w1 !== w2 || it1 !== it2 || tKey(u1) !== tKey(u2) || sing(v1) !== sing(v2) && v1 !== v2 + "s") return null;
    const math = `${a1}*(${n2}/${n1})*(${t2}/${t1})`;
    return result("word-work", math, `each ${sing(w1)} makes ${a1}/(${n1} x ${t1}) ${it1} per ${tKey(u1)}: ${a1} x (${n2}/${n1}) x (${t2}/${t1})`, { goal: "evaluate", notes: ["Assumes every machine works at the same steady rate."] });
  }
  // rate given per unit time: maria types 60 words per minute. how long will it take her to type 1500 words
  if (sents.length === 2 && (m = new RegExp(`^(?:[a-z]+|(?:a|an|the) [a-z]+) ([a-z]+) ${N} ([a-z]+) (?:per|a|an|every|each) ${TU}$`).exec(sents[0]))) {
    const [, v1, r, it, u] = m;
    let mm;
    if ((mm = new RegExp(`^how (?:long|many ${TU}) will it take (?:her|him|them|it|[a-z]+) to ([a-z]+) ${N} ([a-z]+)$`).exec(sents[1]))) {
      const [, u2, v2, n, it2] = mm;
      if (it2 !== it || (u2 && tKey(u2) !== tKey(u)) || !(v1 === v2 + "s" || v1 === v2 + "es" || v1 === v2)) return null;
      return result("word-work", `${n}/${r}`, `time = amount / rate = ${n} ${it} / (${r} ${it} per ${tKey(u)}), in ${tKey(u)}s`, { goal: "evaluate", notes: [`The answer is in ${tKey(u)}s.`] });
    }
  }
  // two or three workers or pipes together
  const SUBJ = String.raw`(?:(?:pipe|machine|pump|printer|tap|hose|worker|crew|team|robot|drain|faucet|inlet|outlet) [a-z](?= )|[a-z]+|(?:a|an|the|one|1|another|the other|a second|the second|a third|the third|his|her|their|my) [a-z]+(?: [a-z]+)?)`;
  const clauses = [];
  let tunit = null, together = null, jobV = null, askUnit = null, want = null, partner = null;
  const addRate = (verb, t, u) => {
    if (tunit && tKey(u) !== tunit) return false;
    tunit = tKey(u);
    clauses.push({ t, neg: NEG_VERB.test(verb) });
    return true;
  };
  const RATE_CL = [
    [C(`(?:working )?(?:alone,? )?${SUBJ}(?: alone| working alone| by (?:him|her|it)self)? can ((?:[a-z]+ ){1,6}?)in ${N} ${TU}(?: working alone| alone| by (?:him|her|it)self)?`), (mm) => addRate(mm[1], mm[2], mm[3])],
    [C(`${SUBJ} (?:takes|needs|would take) ${N} ${TU} to ((?:[a-z]+ ?){1,6})`), (mm) => addRate(mm[3], mm[1], mm[2])],
    [C(`${SUBJ} ([a-z]+s (?:[a-z]+ ){0,5}?)in ${N} ${TU}`), (mm) => (/^(?:is|was|has|does|takes)\b/.test(mm[1]) ? false : addRate(mm[1], mm[2], mm[3]))],
    [C(`${SUBJ} (?:in|takes) ${N} ${TU}`), (mm) => (clauses.length ? addRate("", mm[1], mm[2]) : false)],
  ];
  const TOG = [
    // "together with mark she can paint it in 3 hours": the partner is named, and must not be the one whose rate is known
    [C(`together with ([a-z]+),? (?:he|she|they|[a-z]+) can (?:[a-z]+ ){1,5}?in ${N} ${TU}`), (mm) => { if (NAME_STOP.has(mm[1]) || (tunit && tKey(mm[3]) !== tunit)) return false; tunit = tKey(mm[3]); together = mm[2]; partner = mm[1]; }],
    [C(`(?:working |when working )?together,? (?:the )?(?:2|two|both) [a-z]+ (?:can )?(?:[a-z]+ ){1,5}?in ${N} ${TU}`), (mm) => { if (tunit && tKey(mm[2]) !== tunit) return false; tunit = tKey(mm[2]); together = mm[1]; }],
    [C(`(?:1|one) (?:[a-z]+ )?(?:alone )?(?:takes|needs|can do it in|would take) ${N} ${TU}(?: alone| by itself| working alone)?`), (mm) => addRate("", mm[1], mm[2])],
  ];
  const Q_TOG = [
    [new RegExp(`^(?:if (?:both|they|all 3|all three) (?:are open|work together|are working),? )?how (?:long|many ${TU}) (?:will|would|does|do|should) it take(?: (?:them|both|both of them|them both|the 2|the two|all 3|all three|all of them|the \\w+|both \\w+))?(?: working)?(?: together)?(?: to (?:[a-z]+ ?){1,6})?(?: if (?:both|they) (?:are open|work together))?(?: working together| together)?$`), (mm) => { askUnit = mm[1] || null; want = "together"; }],
    [new RegExp(`^how (?:long|many ${TU}) (?:will|would|do|does) (?:they|both|both of them|all 3|all three)(?: take)?(?: to (?:[a-z]+ ?){1,6})?(?: working together| together)$`), (mm) => { askUnit = mm[1] || null; want = "together"; }],
    [new RegExp(`^how many ${TU} (?:will it take )?to (?:[a-z]+ ?){1,6} (?:with|using) (?:both|all) (?:[a-z]+)$`), (mm) => { askUnit = mm[1]; want = "together"; }],
    [new RegExp(`^how (?:long|many ${TU}) (?:would|will|does) ([a-z]+) (?:take )?(?:alone|by (?:him|her)self|working alone)(?: to (?:[a-z]+ ?){1,6})?$`), (mm) => { if (!partner || mm[2] !== partner) return false; askUnit = mm[1] || null; want = "other"; }],
    [new RegExp(`^how (?:long|many ${TU}) (?:does|would|will) (?:it take )?the other (?:[a-z]+ )?(?:take )?(?:alone|by itself|working alone)?(?: to (?:[a-z]+ ?){1,6})?(?: alone| by itself)?$`), (mm) => { askUnit = mm[1] || null; want = "other"; }],
  ];
  // three at once: 3 workers can do a job in 4, 6 and 12 days respectively
  if ((m = new RegExp(`^(?:2|3|4|two|three|four) [a-z]+ can (?:[a-z]+ ){1,6}?in ${N}, ${N},? and ${N} ${TU} respectively$`).exec(sents[0]))) {
    tunit = tKey(m[4]); clauses.push({ t: m[1] }, { t: m[2] }, { t: m[3] });
    if (!runFacts(sents.slice(1), [], Q_TOG, {})) return null;
  } else if (!runFacts(sents, [...TOG, ...RATE_CL], Q_TOG, {})) return null;
  if (!want || !clauses.length || (askUnit && tKey(askUnit) !== tunit)) return null;
  if (partner && (want !== "other" || new RegExp(`\\b${partner}\\b`).test(sents[0]))) return null;
  const terms = clauses.map((c) => `${c.neg ? "- " : "+ "}1/${c.t}`).join(" ").replace(/^\+ /, "");
  if (want === "together") {
    if (together || clauses.length < 2 || clauses.every((c) => c.neg)) return null;
    // the job only gets done if the combined rate is positive (a drain faster than the tap never fills it)
    if (!(clauses.reduce((a2, c) => a2 + (c.neg ? -1 : 1) / +c.t, 0) > 1e-12)) return impossible("it empties at least as fast as it fills, so the job is never done");
    const math = `${terms} = 1/t`;
    return result("word-work", math, `rates add (jobs per ${tunit}${clauses.some((c) => c.neg) ? "; emptying counts as negative" : ""}): ${math}, t in ${tunit}s`, { variable: "t", notes: [`t is in ${tunit}s.`] });
  }
  if (want === "other") {
    if (!together || clauses.length !== 1 || clauses[0].neg || !(+clauses[0].t > +together)) return null;
    const math = `1/${clauses[0].t} + 1/t = 1/${together}`;
    return result("word-work", math, `rates add: ${math}, t = the other's time alone in ${tunit}s`, { variable: "t", notes: [`t is in ${tunit}s.`] });
  }
  return null;
}

// ---------------------------------------------------------------- distance, speed, time
const LU = String.raw`(km|kilometers?|kilometres?|miles?|mi|m|meters?|metres?|feet|ft|yards?|yd)`;
const lKey = (u) => ({ kilometer: "km", kilometers: "km", kilometre: "km", kilometres: "km", mile: "mi", miles: "mi", meter: "m", meters: "m", metre: "m", metres: "m", foot: "ft", feet: "ft", yard: "yd", yards: "yd" }[u] || u);
const RATEU = String.raw`(km\/h|kph|kmh|km\/hr|mph|mi\/h|m\/s|ft\/s|miles per hour|miles an hour|kilometers per hour|kilometres per hour|km per hour|meters per second|metres per second|feet per second|km an hour)`;
const rKey = (u) => ({ "km/h": ["km", "hour"], kph: ["km", "hour"], kmh: ["km", "hour"], "km/hr": ["km", "hour"], mph: ["mi", "hour"], "mi/h": ["mi", "hour"], "m/s": ["m", "second"], "ft/s": ["ft", "second"], "miles per hour": ["mi", "hour"], "miles an hour": ["mi", "hour"], "kilometers per hour": ["km", "hour"], "kilometres per hour": ["km", "hour"], "km per hour": ["km", "hour"], "km an hour": ["km", "hour"], "meters per second": ["m", "second"], "metres per second": ["m", "second"], "feet per second": ["ft", "second"] }[u]);
const TIME_IN_H = { hour: 1, minute: 1 / 60, second: 1 / 3600 };
const LEN_IN_M = { km: 1000, m: 1, mi: null, ft: null, yd: null };
const MOVERS = String.raw`(?:(?:a|an|the) (?:car|train|bus|truck|plane|boat|bike|bicycle|cyclist|runner|jogger|walker|swimmer|driver|motorcyclist|man|woman|boy|girl|person|ship|jet|rocket|horse|snail|ant|student|hiker|biker)|[a-z]+)`;
const MOVE_V = String.raw`(?:travels|traveled|travelled|goes|went|drives|drove|covers|covered|flies|flew|runs|ran|walks|walked|rides|rode|swims|swam|cycles|cycled|sails|sailed|jogs|jogged|moves|moved|hikes|hiked)`;
const frac = (x) => (Number.isInteger(x) ? String(x) : Number.isInteger(1 / x) ? `(1/${1 / x})` : String(x));
function convertFactor(fromL, fromT, toL, toT) {
  // (length/time) conversion factor, only between metric lengths and between hours/minutes/seconds
  if (!(fromT in TIME_IN_H) || !(toT in TIME_IN_H)) return null;
  let lf;
  if (fromL === toL) lf = 1; else if (LEN_IN_M[fromL] && LEN_IN_M[toL]) lf = LEN_IN_M[fromL] / LEN_IN_M[toL]; else return null;
  return { lf, tf: TIME_IN_H[fromT] / TIME_IN_H[toT] };
}
function distance(sents) {
  let m, mm;
  const [a, b] = sents;
  const HE = String.raw`(?:he|she|it|they|you|[a-z]+|the [a-z]+)`;
  if (sents.length === 2) {
    // speed from distance and time, with an optional requested unit
    if ((m = new RegExp(`^${MOVERS} ${MOVE_V} ${N} ${LU} in ${N} ${TU}$`).exec(a)) && (mm = new RegExp(`^what (?:is|was) (?:its|his|her|their|the) (?:average )?speed(?: in (${RATEU.slice(1, -1)}|km per hour|miles per hour|m per s))?$`).exec(b))) {
      const [, d, lu, t, tu] = m, L = lKey(lu), T = tKey(tu);
      if (!(T in TIME_IN_H)) return null;
      if (mm[1]) {
        const want = rKey(mm[1]); if (!want) return null;
        const f = convertFactor(L, T, want[0], want[1]); if (!f) return null;
        const math = `(${d}*${frac(f.lf)})/(${t}*${frac(f.tf)})`.replace(/\*1\)/g, ")");
        return result("word-distance", math, `speed = distance / time = ${d} ${L} / ${t} ${T}s, converted to ${mm[1]}: ${math}`, { goal: "evaluate", notes: [`The answer is in ${mm[1]}.`] });
      }
      return result("word-distance", `${d}/${t}`, `speed = distance / time = ${d} ${L} / ${t} ${T}s, in ${L} per ${T}`, { goal: "evaluate", notes: [`The answer is in ${L} per ${T}.`] });
    }
    // speed known: how far in t / how long for d
    if ((m = new RegExp(`^(?:if )?(?:${MOVERS}|you) (?:${MOVE_V}|drive|travel|walk|run|ride|fly|cycle) at (?:a (?:constant |steady |average )?speed of )?${N} ?${RATEU}(?: for ${N} ${TU})?$`).exec(a))) {
      const [, r, ru, ft, ftu] = m, R = rKey(ru);
      if (!R) return null;
      if (ft) {
        // "... at r for t. how far does she ride": the time is in the first sentence, possibly in other time units
        if (!(mm = new RegExp(`^how (?:far|many ${LU}) (?:will|does|can|would|do|did) ${HE} (?:[a-z]+)(?: in (?:that|this) time)?$`).exec(b))) return null;
        const T = tKey(ftu);
        if (!(T in TIME_IN_H) || (mm[1] && lKey(mm[1]) !== R[0])) return null;
        const tf = TIME_IN_H[T] / TIME_IN_H[R[1]];
        const tt = tf === 1 ? ft : `${ft}*${frac(tf)}`;
        return result("word-distance", `${r}*${tt}`, `distance = speed x time = ${r} ${ru} x ${ft} ${T}s${tf === 1 ? "" : ` (${tt} ${R[1]}s)`}, in ${R[0]}`, { goal: "evaluate", notes: [`The answer is in ${R[0]}.`] });
      }
      if ((mm = new RegExp(`^how (?:far|many ${LU}) (?:will|does|can|would|do|did) ${HE} (?:[a-z]+) in ${N} ${TU}$`).exec(b))) {
        const [, lu, t, tu] = mm;
        if (tKey(tu) !== R[1] || (lu && lKey(lu) !== R[0])) return null;
        return result("word-distance", `${r}*${t}`, `distance = speed x time = ${r} ${ru} x ${t} ${tKey(tu)}s, in ${R[0]}`, { goal: "evaluate", notes: [`The answer is in ${R[0]}.`] });
      }
      if ((mm = new RegExp(`^how (?:long|many ${TU}) (?:will|does|would) it take(?: (?:him|her|it|them|you|the [a-z]+))? to (?:cover|travel|go|drive|walk|run|ride|fly|cycle|swim|reach a place) ${N} ${LU}(?: away)?$`).exec(b))) {
        const [, tu, d, lu] = mm;
        if (lKey(lu) !== R[0] || (tu && tKey(tu) !== R[1])) return null;
        return result("word-distance", `${d}/${r}`, `time = distance / speed = ${d} ${R[0]} / ${r} ${ru}, in ${R[1]}s`, { goal: "evaluate", notes: [`The answer is in ${R[1]}s.`] });
      }
    }
  }
  if (sents.length === 2 && (m = new RegExp(`^${MOVERS} ${MOVE_V} ${N} ${LU} at (?:a (?:constant |steady |average )?speed of )?${N} ?${RATEU}$`).exec(a))
    && /^how long (?:does|will|did|would) (?:the (?:flight|trip|journey|drive|ride|run|walk)|it) take$/.test(b)) {
    const [, d, lu, r, ru] = m, R = rKey(ru);
    if (!R || lKey(lu) !== R[0]) return null;
    return result("word-distance", `${d}/${r}`, `time = distance / speed = ${d} ${R[0]} / ${r} ${ru}, in ${R[1]}s`, { goal: "evaluate", notes: [`The answer is in ${R[1]}s.`] });
  }
  if (sents.length === 1) {
    // if you drive at 55 miles per hour, how many miles do you travel in 4 hours
    if ((m = new RegExp(`^if (?:you|we|${MOVERS}) (?:drive|travel|walk|run|ride|fly|cycle|go|${MOVE_V}) at ${N} ?${RATEU},? how (?:far|many ${LU}) (?:do|will|would|does|can) (?:you|we|he|she|it|they) (?:[a-z]+) in ${N} ${TU}$`).exec(a))) {
      const [, r, ru, lu, t, tu] = m, R = rKey(ru);
      if (!R || tKey(tu) !== R[1] || (lu && lKey(lu) !== R[0])) return null;
      return result("word-distance", `${r}*${t}`, `distance = speed x time = ${r} ${ru} x ${t} ${tKey(tu)}s, in ${R[0]}`, { goal: "evaluate", notes: [`The answer is in ${R[0]}.`] });
    }
    // average speed for a two-part trip
    if ((m = new RegExp(`^what is the average speed (?:for|of|on) a (?:round )?trip of ${N} ${LU} (?:out|there|one way) at ${N} ?${RATEU} and ${N} ${LU} back at ${N} ?${RATEU}$`).exec(a))) {
      const [, d1, l1, r1, u1, d2, l2, r2, u2] = m, R1 = rKey(u1), R2 = rKey(u2);
      if (!R1 || !R2 || R1.join() !== R2.join() || lKey(l1) !== R1[0] || lKey(l2) !== R1[0]) return null;
      const math = `(${d1} + ${d2})/(${d1}/${r1} + ${d2}/${r2})`;
      return result("word-distance", math, `average speed = total distance / total time = ${math}, in ${u1}`, { goal: "evaluate", notes: [`The answer is in ${u1}.`] });
    }
  }
  // two movers in opposite directions / toward each other
  if (sents.length >= 2) {
    const text = sents.join(". ");
    let r1, r2, D, lu, ru1, ru2, ask, toward = false;
    if ((m = new RegExp(`^(?:2|two) [a-z]+ (?:leave|start from|depart from|set out from|leave from) (?:the same [a-z]+|a [a-z]+|the same place)(?: at the same time)?,? (?:traveling|travelling|going|driving|moving|heading|flying) in opposite directions$`).exec(a))
      && (mm = new RegExp(`^(?:1|one) (?:[a-z]+ )?(?:travels|goes|drives|moves|flies|averages) (?:at )?${N} ?${RATEU} and the other (?:[a-z]+ )?(?:travels |goes |drives |moves |flies |averages )?(?:at )?${N} ?${RATEU}$`).exec(b))) {
      [, r1, ru1, r2, ru2] = mm;
      const c = sents[2];
      let q;
      if (sents.length !== 3 || !(q = new RegExp(`^(?:after how many ${TU}|in how many ${TU}|how (?:long|many ${TU})) (?:will it take )?(?:until |before |for )?(?:will )?they (?:be|are) ${N} ${LU} apart$`).exec(c))) return null;
      const tu = q[1] || q[2] || q[3]; D = q[4]; lu = q[5];
      ask = tu;
    } else if (sents.length === 2 && (m = new RegExp(`^(?:2|two) [a-z]+ (?:start|are|begin|leave from (?:2|two) (?:towns|cities|points))(?: that are)? ${N} ${LU} apart and (?:travel|move|drive|head|ride|walk|fly|run) (?:toward|towards) each other at ${N} ?${RATEU} and ${N} ?${RATEU}(?: respectively)?$`).exec(a))
      && new RegExp(`^(?:how long (?:until |before |will it take (?:for them |until they |before they )?)(?:they )?meet|when will they meet|after how many (hours|minutes) will they meet|how long will it take them to meet)$`).test(b)) {
      [, D, lu, r1, ru1, r2, ru2] = m;
      toward = true;
      const qq = /(hours|minutes)/.exec(b); ask = qq && qq[1];
    } else return m && null;
    const R1 = rKey(ru1), R2 = rKey(ru2);
    if (!R1 || !R2 || R1.join() !== R2.join() || lKey(lu) !== R1[0] || (ask && tKey(ask) !== R1[1])) return null;
    const math = `(${r1} + ${r2})t = ${D}`;
    return result("word-distance", math, `the gap ${toward ? "closes" : "grows"} at ${r1} + ${r2} ${ru1}: ${math}, t in ${R1[1]}s`, { variable: "t", notes: [`t is in ${R1[1]}s.`] });
  }
  return null;
}
function distanceMore(sents) {
  let m, mm;
  // two legs: rides at r1 for t1 and then at r2 for t2
  if (sents.length === 2 && (m = new RegExp(`^${MOVERS} ${MOVE_V} at ${N} ?${RATEU} for ${N} ${TU} and then at ${N} ?${RATEU} for ${N} ${TU}$`).exec(sents[0]))) {
    const [, r1, u1, t1, tu1, r2, u2, t2, tu2] = m, R1 = rKey(u1), R2 = rKey(u2);
    if (!R1 || !R2 || R1.join() !== R2.join() || tKey(tu1) !== R1[1] || tKey(tu2) !== R1[1]) return null;
    if (/^(?:what is the total distance(?: (?:traveled|travelled|covered))?|how far did (?:he|she|it|they) (?:[a-z]+)(?: in total| altogether)?|what distance did (?:he|she|it|they) (?:cover|travel)(?: in total)?)$/.test(sents[1]))
      return result("word-distance", `${r1}*${t1} + ${r2}*${t2}`, `total distance = ${r1} x ${t1} + ${r2} x ${t2}, in ${R1[0]}`, { goal: "evaluate", notes: [`The answer is in ${R1[0]}.`] });
    if (/^what (?:is|was) (?:the|his|her|its) average speed(?: for the (?:whole )?trip)?$/.test(sents[1]))
      return result("word-distance", `(${r1}*${t1} + ${r2}*${t2})/(${t1} + ${t2})`, `average speed = total distance / total time, in ${u1}`, { goal: "evaluate", notes: [`The answer is in ${u1}.`] });
    return null;
  }
  // catch up: A leaves at r1. h hours later B leaves from the same place at r2 (same route). how long after B leaves will it catch up
  if (sents.length === 3 && (m = new RegExp(`^(?:a|the) ([a-z]+) (?:leaves|leaves (?:a|the) [a-z]+|sets out|departs|starts)(?: from (?:a|the) [a-z]+)? (?:traveling |travelling |driving |going )?at ${N} ?${RATEU}$`).exec(sents[0]))
    && (mm = new RegExp(`^${N} ${TU} later,? (?:a|the) (?:second|another) ([a-z]+) (?:leaves|sets out|departs|starts) (?:from )?(?:the same (?:place|point|town|city|station|spot)(?: )?)?(?:traveling |travelling |driving |going )?at ${N} ?${RATEU}(?: (?:following|on|along|traveling on|travelling on|in) the same (?:route|road|direction|path|highway))?$`).exec(sents[1]))
    && /^how (?:long|many hours) (?:after the second [a-z]+ leaves )?will it (?:take (?:the second [a-z]+ )?to )?catch up(?: (?:with|to) the first(?: [a-z]+)?)?$|^how long will it take the second [a-z]+ to catch up(?: (?:with|to) the first(?: [a-z]+)?)?$/.test(sents[2])) {
    const [, v1, r1, u1] = m, [, h, hu, v2, r2, u2] = mm, R1 = rKey(u1), R2 = rKey(u2);
    if (v1 !== v2 || !R1 || !R2 || R1.join() !== R2.join() || tKey(hu) !== R1[1] || !(+r2 > +r1)) return null;
    const math = `${r1}(t + ${h}) = ${r2}t`;
    return result("word-distance", math, `t = time after the second ${v1} leaves; both have covered the same distance: ${math}`, { variable: "t", notes: [`t is in ${R1[1]}s.`] });
  }
  // boat and current
  const BOAT = String.raw`^(?:a|the) (?:boat|ship|swimmer|kayak|canoe|rower|motorboat) (?:goes|travels|rows|sails|swims|moves|covers) ${N} ${LU} (upstream|downstream|with the current|against the current) in ${N} ${TU} and ${N} ${LU} (upstream|downstream|with the current|against the current) in ${N} ${TU}$`;
  if (sents.length === 2 && (m = new RegExp(BOAT).exec(sents[0]))) {
    const [, d1, l1, dir1, t1, tu1, d2, l2, dir2, t2, tu2] = m;
    const down = (d) => /down|with/.test(d);
    if (down(dir1) === down(dir2) || lKey(l1) !== lKey(l2) || tKey(tu1) !== tKey(tu2)) return null;
    const [dd, dt, ud, ut] = down(dir1) ? [d1, t1, d2, t2] : [d2, t2, d1, t1];
    // with the current must be faster than against it, and the boat must make headway upstream
    if (!(+dd / +dt > +ud / +ut && +ud / +ut > 0)) return impossible("going with the current must be faster than going against it");
    let want;
    if (/^(?:what is|find) the speed of the (?:current|stream|river|water)$/.test(sents[1])) want = "c";
    else if (/^(?:what is|find) the speed of the (?:boat|ship|swimmer|kayak|canoe|rower|motorboat) in still water$/.test(sents[1])) want = "b";
    else return null;
    const math = `b + c = ${dd}/${dt}, b - c = ${ud}/${ut}`;
    return result("word-distance", math, `b = speed in still water, c = speed of the current (${lKey(l1)} per ${tKey(tu1)}): downstream b + c, upstream b - c: ${math} (the question asks for ${want})`);
  }
  return null;
}

// ---------------------------------------------------------------- percentages, discounts, tax, tips
const THING = String.raw`(?:[a-z]+ ){0,2}?[a-z]+`;
function percents(sents) {
  const st = {};
  const PRICE_V = String.raw`(?:costs|cost|is priced at|sells for|is|was|has a price of|is marked at|is listed at|regularly costs|normally costs|originally costs|was originally priced at|is originally priced at|that costs|priced at|originally priced at|is originally|originally sells for|usually costs|usually sells for)`;
  const clauses = [
    [C(`(?:the (?:price|cost) of )?(?:a|an|the|your|his|her) ${THING} ${PRICE_V} ${N} dollars`), (m, s) => set1(s, "P", +m[1])],
    [C(`(?:a|an|the) ${N} dollars ${THING}`), (m, s) => set1(s, "P", +m[1])],
    [C(`(?:(?:it|which) )?(?:is |was )?(?:on sale for|on sale at|discounted by|discounted at|marked down by|reduced by|discounted|marked down|reduced|offered at|sold at) ${N}%(?: off| discount)?`), (m, s) => set1(s, "d", +m[1])],
    [C(`(?:there is |with |at |it gets |it has )?a ${N}% (?:discount|reduction|markdown|off)`), (m, s) => set1(s, "d", +m[1])],
    [C(`(?:plus |before |before adding )?(?:a )?${N}% (?:sales )?tax`), (m, s) => set1(s, "t", +m[1])],
    [C(`(?:the )?sales tax (?:rate )?is ${N}%`), (m, s) => set1(s, "t", +m[1])],
    [C(`(?:the )?tax (?:rate )?is ${N}%`), (m, s) => set1(s, "t", +m[1])],
    [C(`(?:you|they|we|he|she|i) (?:leave|leaves|add|adds|give|gives|pay|pays|tip|tips) a ${N}% tip`), (m, s) => set1(s, "tip", +m[1])],
    [C(`after a ${N}% (?:discount|reduction|markdown),? (?:a|an|the) ${THING} (?:costs|sells for|is priced at|is) ${N} dollars`), (m, s) => set1(s, "d", +m[1]) && set1(s, "F", +m[2])],
    [C(`(?:a|the) (?:store|shop|retailer|dealer|merchant) marks up (?:an? |the )?${THING} (?:costing|that costs|which costs|bought for|that cost) ${N} dollars by ${N}%`), (m, s) => set1(s, "cost", +m[1]) && set1(s, "mk", +m[2])],
    [C(`(?:a|the) population of ${N} (increases|grows|rises|decreases|declines|falls|drops) by ${N}%`), (m, s) => set1(s, "B", +m[1]) && set1(s, "g", /increas|grow|rise/.test(m[2]) ? +m[3] : -m[3])],
    [C(`(?:the |a )?(?:price|cost|value|salary|rent|fare|price of (?:a |an |the )?[a-z]+)(?: of (?:a |an |the )?[a-z]+)? (increased|rose|went up|grew|increases|decreased|fell|went down|dropped|decreases|went|changed) from ${N}(?: dollars)? to ${N}(?: dollars)?`), (m, s) => {
      const dir = +m[3] > +m[2] ? "increase" : +m[3] < +m[2] ? "decrease" : null;
      const said = /incr|rose|up|grew/.test(m[1]) ? "increase" : /decr|fell|down|dropped/.test(m[1]) ? "decrease" : dir;
      return dir !== null && said === dir && set1(s, "from", +m[2]) && set1(s, "to", +m[3]) && set1(s, "dir", dir);
    }],
    [C(`(?:a |the )?(?:student|[a-z]+) (?:scored|got|answered|gets|scores|earned) ${N} (?:out of|of) ${N}(?: points| questions| marks)?(?: correctly)?(?: (?:on|in) (?:a|the|his|her) (?:test|exam|quiz))?`), (m, s) => set1(s, "part", +m[1]) && set1(s, "whole", +m[2])],
  ];
  let want = null;
  const Q = [
    [/^what (?:is|was) the (?:sale|new|final|discounted|reduced|selling|retail) price$|^how much does it (?:cost|sell for) (?:now|after the discount|on sale)$|^what does it cost (?:now|on sale)$|^what is the price after the discount$/, () => { want = "newprice"; }],
    [/^how much (?:do|does|will|would|did) (?:you|he|she|they|i) save$|^what is the (?:amount of (?:the )?)?discount(?: amount)?$|^how much is the discount$|^how much money is saved$/, () => { want = "save"; }],
    [/^what is the total(?: cost| price| bill| amount)?(?: including (?:tax|the tax|tip|the tip))?$|^how much (?:is|will be) the total(?: bill| cost)?$|^how much (?:do|does|will) (?:you|he|she|they) pay(?: in total)?$/, () => { want = "total"; }],
    [new RegExp(`^what is the (?:sales )?tax(?: amount)?(?: on (?:a|an|the) ${N} dollars (?:[a-z]+ )?(?:purchase|item|bill|meal|order))?$|^how much (?:is the )?(?:sales )?tax(?: (?:is there|will you pay))?$`), (m, s) => { want = "tax"; return m[1] ? set1(s, "P", +m[1]) : true; }],
    [/^how much is the tip$|^what is the tip(?: amount)?$/, () => { want = "tipamt"; }],
    [/^what (?:was|is) the original price$|^what was the price before the discount$|^how much did it cost before the discount$/, () => { want = "orig"; }],
    [/^what is the new population$|^what is the population after the (?:increase|decrease|change)$/, () => { want = "pop"; }],
    [/^what (?:is|was) the percent(?:age)? (increase|decrease|change)$|^by what percent(?:age)? did (?:it|the price|the cost|the value) (increase|decrease|rise|fall|go up|go down)$/, (m) => { want = "pct:" + (m[1] || m[2]).replace(/rise|go up/, "increase").replace(/fall|go down/, "decrease"); }],
    [/^what percent(?:age)? (?:is that|did (?:he|she|they) (?:get|score)(?: correct| right)?|of the (?:questions|test|points) did (?:he|she|they) get(?: right| correct)?|is (?:his|her|their) score|score is that)$/, () => { want = "score"; }],
  ];
  if (!runFacts(sents, clauses, Q, st) || !want) return null;
  // a discount of 100% or more, or a fall of 100% or more, has no sensible price or population
  if ((st.d !== undefined && !(st.d > 0 && st.d < 100)) || (st.g !== undefined && !(st.g > -100))) return impossible("a discount or decrease must be between 0% and 100%");
  const pct = (p) => `${p}/100`;
  const only = (...keys) => Object.keys(st).every((k) => keys.includes(k));
  const out = (math, interp, extra = {}) => result("word-percent", math, interp, { goal: "evaluate", ...extra });
  switch (want) {
    case "newprice":
      if (st.P !== undefined && st.d !== undefined && only("P", "d")) return out(`${st.P}*(1 - ${pct(st.d)})`, `sale price = price x (1 - discount) = ${st.P} x (1 - ${st.d}%)`);
      if (st.cost !== undefined && only("cost", "mk")) return out(`${st.cost}*(1 + ${pct(st.mk)})`, `selling price = cost x (1 + markup) = ${st.cost} x (1 + ${st.mk}%)`);
      return null;
    case "save":
      return st.P !== undefined && st.d !== undefined && only("P", "d") ? out(`${st.P}*${pct(st.d)}`, `amount saved = price x discount = ${st.P} x ${st.d}%`) : null;
    case "total": {
      if (st.P === undefined || (st.t === undefined && st.tip === undefined) || !only("P", "d", "t", "tip")) return null;
      const f = [`${st.P}`, st.d !== undefined ? `(1 - ${pct(st.d)})` : null, st.t !== undefined ? `(1 + ${pct(st.t)})` : null, st.tip !== undefined ? `(1 + ${pct(st.tip)})` : null].filter(Boolean);
      if (st.d !== undefined && st.tip !== undefined) return null;
      return out(f.join("*"), `total = ${f.join(" x ")}${st.d !== undefined ? " (the discount is applied before the tax)" : ""}`);
    }
    case "tax": return st.P !== undefined && st.t !== undefined && only("P", "t") ? out(`${st.P}*${pct(st.t)}`, `tax = price x rate = ${st.P} x ${st.t}%`) : null;
    case "tipamt": return st.P !== undefined && st.tip !== undefined && only("P", "tip") ? out(`${st.P}*${pct(st.tip)}`, `tip = bill x rate = ${st.P} x ${st.tip}%`) : null;
    case "orig": return st.F !== undefined && only("d", "F") ? result("word-percent", `x*(1 - ${pct(st.d)}) = ${st.F}`, `let x be the original price: x (1 - ${st.d}%) = ${st.F}`, { variable: "x" }) : null;
    case "pop": return st.B !== undefined && only("B", "g") ? out(`${st.B}*(1 + ${pct(st.g)})`, `new population = ${st.B} x (1 ${st.g < 0 ? "-" : "+"} ${Math.abs(st.g)}%)`) : null;
    case "score": return st.part !== undefined && only("part", "whole") && st.part <= st.whole ? out(`${st.part}/${st.whole}*100`, `percent = ${st.part}/${st.whole} x 100`) : null;
    default:
      if (want.startsWith("pct:") && st.from !== undefined && only("from", "to", "dir")) {
        const dir = want.slice(4);
        if (dir !== "change" && dir !== st.dir) return null;
        if (st.from === 0) return null;
        const math = st.dir === "increase" ? `(${st.to} - ${st.from})/${st.from}*100` : `(${st.from} - ${st.to})/${st.from}*100`;
        return out(math, `percent ${st.dir} = ${st.dir === "increase" ? "(new - old)" : "(old - new)"}/old x 100 = ${math}`);
      }
      return null;
  }
}
function percentOf(sents) {
  let m;
  if (sents.length !== 1) return null;
  let p, v;
  if ((m = new RegExp(`^${N}% of what (?:number|amount|value) is ${N}$`).exec(sents[0]))) [, p, v] = m;
  else if ((m = new RegExp(`^${N} is ${N}% of what (?:number|amount|value)$`).exec(sents[0]))) [, v, p] = m;
  if (p !== undefined) return result("word-percent", `${p}/100*x = ${v}`, `let x be the number: ${p}% of x = ${v}`, { variable: "x" });
  if ((m = new RegExp(`^what percent(?:age)? of ${N} is ${N}$`).exec(sents[0]))) return result("word-percent", `${m[2]}/${m[1]}*100`, `percent = ${m[2]}/${m[1]} x 100`, { goal: "evaluate" });
  return null;
}

// ---------------------------------------------------------------- interest
const FREQ = { annually: 1, yearly: 1, "semi-annually": 2, semiannually: 2, quarterly: 4, monthly: 12, weekly: 52, daily: 365 };
const FREQ_RE = String.raw`(annually|yearly|semi-annually|semiannually|quarterly|monthly|weekly|daily|continuously)`;
const PER = String.raw`(?: (?:per year|a year|per annum|annually|p\.?a\.?|annual interest|interest|annual))?`;
function amountText(P, r, t, freq) {
  if (freq === "continuously") return { math: `${P}*e^(${r}/100*${t})`, how: `A = P e^(rt) with P = ${P}, r = ${r}%, t = ${t}` };
  const n = FREQ[freq];
  return { math: `${P}*(1 + ${r}/100/${n})^(${n}*${t})`, how: `A = P (1 + r/n)^(nt) with P = ${P}, r = ${r}%, n = ${n}, t = ${t}` };
}
function interest(sents) {
  let m;
  const t = sents.join(". ");
  const one = sents.length === 1 ? sents[0] : null;
  const ev = (math, interp, notes = []) => result("word-interest", math, interp, { goal: "evaluate", notes });
  // simple interest
  if (one && (m = new RegExp(`^how much (?:simple )?interest (?:is|will be|would be) (?:earned|paid|charged|owed) on ${N} dollars at ${N}%${PER}(?: simple interest)?(?: per year| a year| per annum)? for ${N} years?$`).exec(one))) {
    if (!/simple/.test(one)) return null;
    return ev(`${m[1]}*${m[2]}/100*${m[3]}`, `simple interest I = P r t = ${m[1]} x ${m[2]}% x ${m[3]}`);
  }
  if (sents.length === 2 && (m = new RegExp(`^(?:a|the) (?:loan|deposit|investment) of ${N} dollars (?:is taken )?at ${N}% simple interest(?: per year| a year| per annum)? for ${N} years?$`).exec(sents[0]))) {
    if (/^what is the total amount (?:to be repaid|owed|due|to repay|to be paid back|paid back)$|^how much (?:must be repaid|is owed|will be owed|must be paid back) in total$/.test(sents[1]))
      return ev(`${m[1]}*(1 + ${m[2]}/100*${m[3]})`, `amount = P (1 + r t) = ${m[1]} (1 + ${m[2]}% x ${m[3]})`);
    if (/^(?:what is|how much is) the (?:simple )?interest$/.test(sents[1])) return ev(`${m[1]}*${m[2]}/100*${m[3]}`, `simple interest I = P r t = ${m[1]} x ${m[2]}% x ${m[3]}`);
    return null;
  }
  if (one && (m = new RegExp(`^at what (?:simple interest )?rate(?: of simple interest)? will ${N} dollars (?:earn|give|yield) ${N} dollars(?: (?:in |of )?(?:simple )?interest)? in ${N} years$`).exec(one)) && /simple/.test(one))
    return result("word-interest", `${m[1]}*r/100*${m[3]} = ${m[2]}`, `simple interest P r t = I with r in percent: ${m[1]} x r% x ${m[3]} = ${m[2]}`, { variable: "r", notes: ["r is the yearly rate in percent."] });
  if (one && (m = new RegExp(`^how many years will it take (?:for )?${N} dollars to earn ${N} dollars (?:in|of) simple interest at ${N}%${PER}$`).exec(one)))
    return result("word-interest", `${m[1]}*${m[3]}/100*t = ${m[2]}`, `simple interest P r t = I: ${m[1]} x ${m[3]}% x t = ${m[2]}`, { variable: "t" });
  if (one && (m = new RegExp(`^what (?:principal|amount|sum)(?: of money)? will (?:earn|give|yield) ${N} dollars (?:in|of) simple interest at ${N}%${PER} (?:in|over|for) ${N} years$`).exec(one)))
    return result("word-interest", `P*${m[2]}/100*${m[3]} = ${m[1]}`, `simple interest P r t = I: P x ${m[2]}% x ${m[3]} = ${m[1]}`, { variable: "P" });
  // compound interest
  if (one && (m = new RegExp(`^how much will ${N} dollars be worth after ${N} years at ${N}%${PER} compounded ${FREQ_RE}$`).exec(one))) {
    const a = amountText(m[1], m[3], m[2], m[4]); return ev(a.math, a.how);
  }
  if (one && (m = new RegExp(`^(?:find|what is|calculate) the (?:final )?(?:amount|balance|value) after ${N} years if ${N} dollars is invested at ${N}%${PER} compounded ${FREQ_RE}$`).exec(one))) {
    const a = amountText(m[2], m[3], m[1], m[4]); return ev(a.math, a.how);
  }
  if (one && (m = new RegExp(`^(?:find |what is |calculate )?(?:the )?compound interest (?:on|earned on|for) ${N} dollars at ${N}%${PER}(?: compounded ${FREQ_RE})? for ${N} years$`).exec(one))) {
    const a = amountText(m[1], m[2], m[4], m[3] || "annually");
    return ev(`${a.math} - ${m[1]}`, `compound interest = A - P, ${a.how}${m[3] ? "" : " (compounded yearly: no period was given)"}`, m[3] ? [] : ["Compounded once a year (no period was given)."]);
  }
  if (sents.length === 2 && (m = new RegExp(`^${N} dollars (?:is|was) (?:invested|deposited|put) (?:in an account )?at ${N}%${PER} compounded ${FREQ_RE} for ${N} years$`).exec(sents[0]))) {
    const a = amountText(m[1], m[2], m[4], m[3]);
    if (/^(?:what is|find|calculate) the (?:final |new )?(?:amount|balance|value)(?: in the account)?(?: after .*)?$|^how much (?:is in the account|will there be|will it be worth|money will there be)(?: at the end)?$/.test(sents[1])) return ev(a.math, a.how);
    if (/^(?:how much|what is the) (?:compound )?interest (?:is earned|was earned|will be earned|earned)?$/.test(sents[1])) return ev(`${a.math} - ${m[1]}`, `interest = A - P, ${a.how}`);
    return null;
  }
  return null;
}

// ---------------------------------------------------------------- perimeter, area, volume
const GU = String.raw`(?: (?:square |sq |cubic |cu )?(?:cm|m|mm|km|in|inches|inch|ft|feet|foot|yards?|yd|meters?|metres?|centimeters?|centimetres?|miles?|units?)(?:\^?[23])?)?`;
const SHAPES = String.raw`(rectangle|rectangular [a-z]+|square(?: [a-z]+)?|cube|triangle|circle|circular [a-z]+|right triangle)`;
const shapeKey = (s) => (/^rect/.test(s) ? "rectangle" : /^square/.test(s) ? "square" : /^circ/.test(s) ? "circle" : s);
const PROPS = String.raw`(length|width|perimeter|area|base|height|radius|diameter|side length|side|volume|surface area|edge length|edge|circumference)`;
const propKey = (p) => ({ "side length": "side", "edge length": "side", edge: "side" }[p] || p);
function geometry(sents) {
  const st = { shape: null, v: {}, rel: [] };
  const setShape = (s) => { const k = shapeKey(s); if (st.shape && st.shape !== k) return false; st.shape = k; return true; };
  const setV = (p, x) => { const k = propKey(p); if (st.v[k] !== undefined && st.v[k] !== +x) return false; st.v[k] = +x; return true; };
  const REL = String.raw`(?:the |its )?(length|width) (?:of (?:a|the) (?:rectangle|rectangular [a-z]+) )?is ((?:[a-z0-9.()/%]+ ){0,8}?(?:its|the) (?:length|width))`;
  const clauses = [
    [C(`(?:a|the) right triangle has legs (?:of (?:length )?)?${N}${GU} and ${N}${GU}`), (m) => setShape("right triangle") && setV("leg1", m[1]) && setV("leg2", m[2])],
    [C(REL), (m) => { st.rel.push(`the ${m[1]} is ${m[2].replace(/\bits\b/g, "the")}`); if (!st.shape) st.shape = "rectangle"; return st.shape === "rectangle"; }],
    [C(`(?:a|the) ${SHAPES} (?:has|with)`), (m) => setShape(m[1])],
    [C(`(?:a|the) ${SHAPES} is ${N}${GU} long`), (m, s) => setShape(m[1]) && setV("length", m[2])],
    [C(`${N}${GU} (long|wide|high|tall)`), (m) => setV(m[2] === "long" ? "length" : m[2] === "wide" ? "width" : "height", m[1])],
    [C(`(?:a|an|its) ${PROPS} (?:of |= ?)?${N}${GU}`), (m) => setV(m[1], m[2])],
    [C(`the ${PROPS} of (?:a|the) ${SHAPES} is ${N}${GU}`), (m) => setShape(m[2]) && setV(m[1], m[3])],
    [C(`(?:the|its) ${PROPS} is ${N}${GU}`), (m) => setV(m[1], m[2])],
  ];
  let want = null;
  const Q = [
    [/^(?:what is|find) the length of (?:one|1|each|an|a) (?:edge|side)$/, () => { want = "side"; }],
    [new RegExp(`^(?:what is|find|calculate) the ${PROPS} of (?:a|the) ${SHAPES} (?:with|that has|having|whose) (.+)$`), (m, s) => { want = propKey(m[1]); if (!setShape(m[2])) return false; if (!consume(m[3].replace(new RegExp(`^(?:its |the )?${PROPS} is `), "a $1 of "), clauses, s)) return false; }],
    [new RegExp(`^(?:what is|find|calculate|determine|how (?:long|big) is) (?:its|the) ${PROPS}(?: of (?:the|one|each) (?:${SHAPES}|side|edge))?$`), (m) => { want = propKey(m[1]); }],
    [/^(?:how long is|what is|find) the hypotenuse$/, () => { want = "hypotenuse"; }],
    [/^(?:what are|find) (?:the|its) dimensions$/, () => { want = "dimensions"; }],
  ];
  if (!runFacts(sents, clauses, Q, st) || !want || !st.shape) return null;
  const v = st.v, out = (math, interp) => result("word-geometry", math, interp, { goal: "evaluate", notes: ["The answer is in the units of the problem."] });
  const has = (...k) => k.every((x) => v[x] !== undefined) && Object.keys(v).length === k.length && !st.rel.length;
  switch (st.shape) {
    case "rectangle": {
      if (st.rel.length) {
        if (st.rel.length !== 1) return null;
        const nouns = [noun("the length", "l"), noun("the width", "w")];
        const e = readEquation(st.rel[0], nouns, ["l", "w"]);
        if (!e || e.ambiguous) return null;
        const keys = Object.keys(v);
        if (keys.length !== 1) return null;
        if (keys[0] === "perimeter") {
          const math = `${e.text}, 2l + 2w = ${v.perimeter}`;
          if (!sensible(math, ["l", "w"], (x) => x > 0)) return impossible("the length or the width would not be positive");
          if (!["length", "width", "dimensions"].includes(want)) return null;
          return result("word-geometry", math, `l = length, w = width: ${math}${want !== "dimensions" ? ` (the question asks for ${want === "length" ? "l" : "w"})` : ""}`);
        }
        if (keys[0] === "area") {
          const mm = /^([lw]) = (.+)$/.exec(e.text);
          if (!mm) return null;
          const sub = mm[1], other = sub === "l" ? "w" : "l";
          // the relation must give one side in terms of the other only
          if (mm[2].includes(sub) || !mm[2].includes(other) || /[a-km-vx-z]/.test(mm[2])) return null;
          const wantVar = want === "length" ? "l" : want === "width" ? "w" : null;
          if (wantVar !== other) return null; // the substituted side would need a second step
          const math = `${other}*(${mm[2]}) = ${v.area}, ${other} > 0, ${mm[2]} > 0`;
          return result("word-geometry", math, `let ${other} be the ${other === "l" ? "length" : "width"}, so the ${sub === "l" ? "length" : "width"} is ${mm[2]}; area = length x width: ${math.split(",")[0]}, both sides positive`, { variable: other });
        }
        return null;
      }
      const L = v.length, W = v.width;
      if (L !== undefined && W !== undefined && has("length", "width")) {
        if (want === "area") return out(`${L}*${W}`, `area = length x width = ${L} x ${W}`);
        if (want === "perimeter") return out(`2*(${L} + ${W})`, `perimeter = 2(length + width) = 2(${L} + ${W})`);
        return null;
      }
      if (v.area !== undefined && (W !== undefined || L !== undefined) && Object.keys(v).length === 2) {
        const k = W !== undefined ? W : L;
        if ((want === "length" && W !== undefined) || (want === "width" && L !== undefined)) return out(`${v.area}/${k}`, `${want} = area / ${W !== undefined ? "width" : "length"} = ${v.area}/${k}`);
        return null;
      }
      if (v.perimeter !== undefined && (W !== undefined || L !== undefined) && Object.keys(v).length === 2) {
        const k = W !== undefined ? W : L;
        if ((want === "length" && W !== undefined) || (want === "width" && L !== undefined)) return out(`${v.perimeter}/2 - ${k}`, `${want} = perimeter/2 - ${W !== undefined ? "width" : "length"} = ${v.perimeter}/2 - ${k}`);
        return null;
      }
      return null;
    }
    case "square": {
      const keys = Object.keys(v);
      if (keys.length !== 1) return null;
      const side = { side: `${v.side}`, perimeter: `${v.perimeter}/4`, area: `sqrt(${v.area})` }[keys[0]];
      if (!side) return null;
      const f = { side: `${side}`, perimeter: `4*(${side})`, area: `(${side})^2` }[want];
      if (!f || want === keys[0]) return null;
      const sideFrom = keys[0] === "perimeter" ? `perimeter / 4 = ${v.perimeter}/4` : `sqrt(area) = sqrt(${v.area})`;
      return out(f, want === "side" ? `side = ${sideFrom}` : `side = ${sideFrom}; ${want} = ${want === "area" ? "side^2" : "4 x side"}`);
    }
    case "cube": {
      const keys = Object.keys(v);
      if (keys.length !== 1) return null;
      const side = { side: `${v.side}`, volume: `(${v.volume})^(1/3)`, "surface area": `sqrt(${v["surface area"]}/6)` }[keys[0]];
      const f = side && { side, volume: `(${side})^3`, "surface area": `6*(${side})^2` }[want];
      if (!f || want === keys[0]) return null;
      return out(f, `edge = ${keys[0] === "side" ? v.side : keys[0] === "volume" ? "cube root of the volume" : "sqrt(surface area / 6)"}; ${want} = ${want === "volume" ? "edge^3" : want === "surface area" ? "6 edge^2" : "edge"}`);
    }
    case "triangle":
      if (want === "area" && has("base", "height")) return out(`${v.base}*${v.height}/2`, `area = base x height / 2 = ${v.base} x ${v.height} / 2`);
      if (want === "height" && has("base", "area")) return out(`2*${v.area}/${v.base}`, `height = 2 x area / base`);
      if (want === "base" && has("height", "area")) return out(`2*${v.area}/${v.height}`, `base = 2 x area / height`);
      return null;
    case "right triangle":
      if (want === "hypotenuse" && has("leg1", "leg2")) return out(`sqrt(${v.leg1}^2 + ${v.leg2}^2)`, `Pythagoras: hypotenuse = sqrt(${v.leg1}^2 + ${v.leg2}^2)`);
      return null;
    case "circle": {
      const keys = Object.keys(v);
      if (keys.length !== 1) return null;
      const r = { radius: `${v.radius}`, diameter: `${v.diameter}/2`, circumference: `${v.circumference}/(2*pi)`, area: `sqrt(${v.area}/pi)` }[keys[0]];
      const f = r && { radius: r, diameter: `2*(${r})`, circumference: `2*pi*(${r})`, area: `pi*(${r})^2` }[want];
      if (!f || want === keys[0]) return null;
      const rFrom = { radius: `${r}`, diameter: `diameter / 2 = ${r}`, circumference: `circumference / (2 pi) = ${r}`, area: `sqrt(area / pi) = ${r}` }[keys[0]];
      if (want === "radius") return out(f, `radius = ${rFrom}`);
      return out(f, `radius r = ${rFrom}; ${want} = ${{ diameter: "2r", circumference: "2 pi r", area: "pi r^2" }[want]}`);
    }
  }
  return null;
}
function boxVolume(sents) {
  let m;
  if (sents.length === 1 && (m = new RegExp(`^(?:what is|find) the (volume|surface area) of (?:a|the) (?:box|rectangular box|rectangular prism|cuboid|room|tank|container) (?:that is|measuring|with dimensions|of) ${N}${GU} (?:by|x) ${N}${GU} (?:by|x) ${N}${GU}$`).exec(sents[0]))) {
    const [, q, a, b, c] = m;
    return q === "volume" ? result("word-geometry", `${a}*${b}*${c}`, `volume = length x width x height = ${a} x ${b} x ${c}`, { goal: "evaluate" })
      : result("word-geometry", `2*(${a}*${b} + ${a}*${c} + ${b}*${c})`, `surface area = 2(lw + lh + wh)`, { goal: "evaluate" });
  }
  return null;
}

// ---------------------------------------------------------------- probability of simple events
const PREDS = [
  [/^(?:an )?even(?: number)?$/, (k) => k % 2 === 0, "even"],
  [/^(?:an )?odd(?: number)?$/, (k) => k % 2 === 1, "odd"],
  [/^(?:a )?prime(?: number)?$/, (k) => k > 1 && [...Array(k).keys()].slice(2).every((d) => k % d), "prime"],
  [/^(?:a )?(?:number )?(?:greater|more|larger|bigger|higher) than (\d+)$/, (k, a) => k > a, "greater than"],
  [/^(?:a )?(?:number )?(?:less|smaller|lower|fewer) than (\d+)$/, (k, a) => k < a, "less than"],
  [/^(?:a )?(?:number )?(?:at least|greater than or equal to|no less than) (\d+)$/, (k, a) => k >= a, "at least"],
  [/^(?:a )?(?:number )?(?:at most|less than or equal to|no more than) (\d+)$/, (k, a) => k <= a, "at most"],
  [/^(?:a )?multiple of (\d+)$/, (k, a) => a > 0 && k % a === 0, "multiple of"],
  [/^(?:a )?(?:number )?divisible by (\d+)$/, (k, a) => a > 0 && k % a === 0, "divisible by"],
  [/^(?:a )?factor of (\d+)$|^(?:a )?divisor of (\d+)$/, (k, a) => a % k === 0, "factor of"],
  [/^(?:a )?perfect square$/, (k) => Number.isInteger(Math.sqrt(k)), "perfect square"],
  [/^(?:a |an )?(\d+)$/, (k, a) => k === a, "equal to"],
];
function favourable(pred, n) {
  const p = pred.replace(/^(?:a|an) /, "");
  for (const [re, f] of PREDS) {
    const m = re.exec(p);
    if (!m) continue;
    const a = m[1] !== undefined ? +m[1] : m[2] !== undefined ? +m[2] : undefined;
    if (a === 0 && /multiple|divisible|factor/.test(re.source)) return null; // "a multiple of 0" is not a real event
    const ks = [];
    for (let k = 1; k <= n; k++) if (f(k, a)) ks.push(k);
    return ks;
  }
  return null;
}
const CARDS = { ace: 4, king: 4, queen: 4, jack: 4, heart: 13, spade: 13, club: 13, diamond: 13, "red card": 26, "black card": 26, "face card": 12 };
function probability(sents) {
  let m, mm;
  const P = (math, interp) => result("word-probability", math, interp, { goal: "evaluate" });
  // coloured objects in a container
  const CONT = String.raw`(?:a|the|one) (?:bag|box|jar|urn|basket|drawer|bowl|hat|container|can|bucket|pouch|sack|tin)`;
  if ((m = new RegExp(`^${CONT} (?:contains|has|holds|is filled with) (.+)$`).exec(sents[0]))) {
    const items = m[1].split(/,? and |, /);
    const counts = new Map();
    let nounW = null;
    for (const it of items) {
      const x = /^(\d+) ([a-z]+)(?: ([a-z]+))?$/.exec(it);
      if (!x) return null;
      const col = x[2], nn = x[3] ? sing(x[3]) : null;
      if (nn) { if (nounW && nounW !== nn) return null; nounW = nn; }
      if (counts.has(col)) return null;
      counts.set(col, +x[1]);
    }
    if (counts.size < 2) return null;
    const total = [...counts.values()].reduce((a, b) => a + b, 0);
    const NN = String.raw`(?: ${nounW || "[a-z]+"}s?| one)?`;
    const COL = String.raw`([a-z]+)`;
    const rest = sents.slice(1).join(". ");
    let draw2 = null;
    let q = rest;
    if ((mm = /^(2|two) [a-z]+ are (?:drawn|picked|chosen|selected|taken|pulled out)(?: at random)?(?: one after the other)?,? (without|with) replacement\. (.+)$/.exec(rest))) { draw2 = mm[2]; q = mm[3]; }
    q = q.replace(/^(?:if |when )?(?:1|one|a) [a-z]+ is (?:drawn|picked|chosen|selected|taken|pulled out)(?: at random)?,? /, "");
    const col = (c) => (counts.has(c) ? counts.get(c) : null);
    if (draw2) {
      if (!(mm = new RegExp(`^what is the probability (?:that )?(?:both|both of them|they) are ${COL}$`).exec(q))) return null;
      const r = col(mm[1]); if (r === null) return null;
      return draw2 === "without" ? P(`binomial(${r}, 2)/binomial(${total}, 2)`, `2 drawn without replacement, both ${mm[1]}: (${r}/${total}) x (${r - 1}/${total - 1})`)
        : P(`(${r}/${total})^2`, `2 independent draws with replacement, both ${mm[1]}: (${r}/${total})^2`);
    }
    if ((mm = new RegExp(`^what is the probability (?:of (?:drawing|picking|choosing|selecting|getting|pulling out|taking) (?:a|an) (not )?${COL}${NN}(?: or (?:a |an )?${COL}${NN})?|(?:that )?(?:it|the [a-z]+|a randomly (?:chosen|drawn|picked|selected) [a-z]+) is (not )?${COL}(?: or ${COL})?)(?: at random)?$`).exec(q))) {
      const neg = mm[1] || mm[4], c1 = mm[2] || mm[5], c2 = mm[3] || mm[6];
      const a = col(c1), b = c2 ? col(c2) : 0;
      if (a === null || b === null || c1 === c2) return null;
      if (neg && c2) return null;
      const fav = neg ? total - a : a + b;
      return P(`${fav}/${total}`, `${neg ? `not ${c1}: ${total} - ${a}` : c2 ? `${c1} or ${c2}: ${a} + ${b}` : `${c1}: ${a}`} favourable out of ${total} equally likely`);
    }
    return null;
  }
  // die, spinner or number chosen from 1..n
  let n = null, q = null;
  if (sents.length === 1 && (m = /^what is the probability of (?:rolling|getting|throwing) (?:a |an )?(.+?) (?:on|with|when rolling) (?:a |one )?(?:fair |single |standard |regular |normal )*(?:(\d+) sided |six sided )?(?:die|dice|number cube)$/.exec(sents[0]))) { n = m[2] ? +m[2] : 6; q = m[1]; }
  else if (sents.length === 2 && (m = /^a spinner (?:has|is divided into) (\d+) equal (?:sections|parts|sectors|regions|spaces) numbered 1 (?:to|through) (\d+)$/.exec(sents[0])) && m[1] === m[2]
    && (mm = /^what is the probability of (?:landing on|spinning|getting|the spinner landing on) (?:a |an )?(.+)$/.exec(sents[1]))) { n = +m[1]; q = mm[1]; }
  else if (sents.length === 2 && (m = /^a (?:whole )?number is (?:chosen|picked|selected|drawn) at random from (?:the (?:whole )?numbers |the integers )?1 (?:to|through) (\d+)(?: inclusive)?$/.exec(sents[0]))
    && (mm = /^what is the probability (?:that )?(?:it|the number) is (?:a |an )?(.+)$/.exec(sents[1]))) { n = +m[1]; q = mm[1]; }
  if (n) {
    if (!(n >= 2 && n <= 1000)) return null;
    const ks = favourable(q.replace(/ number$/, " number"), n);
    if (!ks) return null;
    const shown = ks.length <= 12 ? `{${ks.join(", ")}}` : `${ks.length} numbers`;
    return P(`${ks.length}/${n}`, `outcomes 1 to ${n}, equally likely; favourable ${shown}: ${ks.length}/${n}`);
  }
  // one fair coin / n coins all heads
  if (sents.length === 1 && (m = /^what is the probability of (?:getting|flipping|tossing|landing on) (?:a )?(heads?|tails?) (?:when|on|if|by) (?:flipping|tossing|you flip|you toss) a (?:fair )?coin$/.exec(sents[0]))) return P("1/2", "a fair coin: 1 of 2 equally likely faces");
  if (sents.length === 1 && (m = /^what is the probability of (?:getting )?(\d+) (heads|tails) (?:when|if|on) (?:flipping|tossing|you flip|you toss) (\d+) (?:fair )?coins$/.exec(sents[0])) && m[1] === m[3])
    return P(`(1/2)^${m[3]}`, `every one of ${m[3]} independent fair coins shows ${m[2]}: (1/2)^${m[3]}`);
  // one card from a standard deck
  if (sents.length === 2 && /^a card is (?:drawn|picked|chosen|selected|dealt) (?:at random )?from a (?:standard |well shuffled |shuffled |normal )*(?:deck(?: of (?:52 )?(?:playing )?cards)?|52 card deck)$/.test(sents[0])
    && (m = /^what is the probability (?:that )?it is (?:a|an) ([a-z]+(?: card)?)$/.exec(sents[1]))) {
    const k = m[1].replace(/s$/, "");
    return CARDS[k] ? P(`${CARDS[k]}/52`, `${CARDS[k]} of the 52 equally likely cards are ${k}s`) : null;
  }
  // complement: the probability of rain tomorrow is 0.3. what is the probability that it does not rain
  if (sents.length === 2 && (m = /^the probability (?:of|that) (?:it will )?([a-z]+)(?: [a-z]+)? is (\d*\.\d+|\(\d+\/\d+\)|\d+%)$/.exec(sents[0]))
    && (mm = /^what is the probability (?:that )?(?:it (?:does not|doesn't|will not|won't) ([a-z]+)(?: [a-z]+)?|of no ([a-z]+)(?: [a-z]+)?)$/.exec(sents[1]))) {
    const ev = m[1], neg = mm[1] || mm[2];
    const stem = (w) => w.replace(/(?:s|ing)$/, "");
    if (stem(ev) !== stem(neg)) return null;
    const p = /%$/.test(m[2]) ? `${m[2].slice(0, -1)}/100` : m[2];
    return P(`1 - ${p}`, `complement: P(not ${ev}) = 1 - P(${ev}) = 1 - ${p}`);
  }
  return null;
}

// ---------------------------------------------------------------- unit rates and proportions
const UNITW = String.raw`([a-z]+)`;
function unitRates(sents) {
  let m, mm;
  const E = (math, interp, notes = []) => result("word-rate", math, interp, { goal: "evaluate", notes });
  const same = (a, b) => sing(a) === sing(b);
  const text = sents.join(". ");
  // price of n items
  const COSTQ = (item) => [
    [new RegExp(`^how much (?:do|does|would|will) ${N} ${item}(?: of [a-z]+)? cost$`), (x) => x[1]],
    [new RegExp(`^what (?:is|would be|will be) the (?:cost|price) of ${N} ${item}(?: of [a-z]+)?$`), (x) => x[1]],
    [new RegExp(`^how much (?:does|would|will) (?:1|one|a|an|each) ${item} cost$|^what is the (?:cost|price) of (?:1|one|a|an|each) ${item}$|^what is the (?:unit price|price per ${item}|cost per ${item})$`), () => "1"],
  ];
  const item0 = String.raw`([a-z]+(?: [a-z]+)?)`;
  let n1, it, price, rest = sents.slice(1);
  {
    // "N items cost P dollars" or "N units of X cost P dollars", optionally with ", how much ..." in the same sentence
    const one = sents.length === 1 ? ",? (how .+|what .+)" : "";
    if ((m = new RegExp(`^(?:if )?${N} ([a-z]+) of [a-z]+ costs? ${N} dollars${one}$`).exec(sents[0]))) { [, n1, it, price] = m; if (one) rest = [m[4]]; }
    else if ((m = new RegExp(`^(?:if )?${N} ${item0} costs? ${N} dollars${one}$`).exec(sents[0]))) { [, n1, it, price] = m; if (one) rest = [m[4]]; }
  }
  if (n1 && rest.length === 1) {
    const head = it.split(" ")[0];
    for (const w of [head, it]) {
      const I = String.raw`(?:${w.replace(/s$/, "")}s?|${w})`;
      for (const [re, g] of COSTQ(I)) { const x = re.exec(rest[0]); if (x) { const k = g(x); return E(`${price}/${n1}*${k}`, `unit price ${price}/${n1} dollars per ${sing(head)}, times ${k}`, ["The answer is in dollars."]); } }
    }
  }
  // a 12 ounce box of cereal costs 3.60 dollars. what is the price per ounce
  if (sents.length === 2 && (m = new RegExp(`^(?:a|an|the) ${N} ${UNITW} (?:box|bag|bottle|can|jar|pack|package|carton|tub|bar|jug) of [a-z]+ costs ${N} dollars$`).exec(sents[0]))
    && (mm = new RegExp(`^what is the (?:price|cost|unit price) per ${UNITW}$`).exec(sents[1])) && same(mm[1], m[2]))
    return E(`${m[3]}/${m[1]}`, `price per ${sing(m[2])} = ${m[3]} / ${m[1]}`, ["The answer is in dollars."]);
  // earnings
  if (sents.length === 2 && (m = new RegExp(`^(?:a |an |the )?[a-z]+ (?:earns|makes|is paid|gets paid|gets) ${N} dollars (?:for|in) ${N} ${TU}(?: of work)?$`).exec(sents[0]))
    && (mm = new RegExp(`^how much (?:does|do|did) (?:he|she|they|it|the [a-z]+|[a-z]+) (?:earn|make|get paid|get) (?:per|an|a|each) ${TU}$`).exec(sents[1])) && tKey(mm[1]) === tKey(m[3]))
    return E(`${m[1]}/${m[2]}`, `pay per ${tKey(m[3])} = ${m[1]} / ${m[2]}`, ["The answer is in dollars."]);
  if (sents.length === 2 && (m = new RegExp(`^(?:a |an |the )?[a-z]+ (?:earns|makes|is paid|gets paid|gets) ${N} dollars (?:per|an|a|each) ${TU}$`).exec(sents[0]))
    && (mm = new RegExp(`^how much (?:does|will|would|did|do) (?:he|she|they|it|the [a-z]+|[a-z]+) (?:earn|make|get paid|get) (?:in|for) ${N} ${TU}$`).exec(sents[1])) && tKey(mm[2]) === tKey(m[2]))
    return E(`${m[1]}*${mm[1]}`, `pay = rate x time = ${m[1]} x ${mm[1]}`, ["The answer is in dollars."]);
  // a car uses 8 gallons of gas to travel 240 miles. how many miles per gallon does it get
  if (sents.length === 2 && (m = new RegExp(`^(?:a|an|the) [a-z]+ uses ${N} ${UNITW}(?: of [a-z]+)? to (?:travel|go|drive|cover|run) ${N} ${UNITW}$`).exec(sents[0]))
    && (mm = new RegExp(`^how many ${UNITW} per ${UNITW} does it (?:get|do|make|travel)$`).exec(sents[1])) && same(mm[1], m[4]) && same(mm[2], m[2]))
    return E(`${m[3]}/${m[1]}`, `${m[4]} per ${sing(m[2])} = ${m[3]} / ${m[1]}`);
  // a fixed machine or person at a steady rate: amount is proportional to the other quantity
  const SUB = String.raw`(?:a|an|the) [a-z]+(?: [a-z]+)?`;
  if (sents.length <= 2) {
    let a1, u1, a2, u2, q;
    const V = String.raw`([a-z]+s)`;
    if (sents.length === 2 && (m = new RegExp(`^(?:if )?${SUB} ${V} ${N} ${UNITW}(?: of [a-z]+)? (?:in|on|per|every|for|using|with) ${N} ${UNITW}(?: of [a-z]+)?$`).exec(sents[0]))) { [, , a1, u1, a2, u2] = m; q = sents[1]; }
    else if (sents.length === 1 && (m = new RegExp(`^(?:if )?${SUB} ${V} ${N} ${UNITW}(?: of [a-z]+)? (?:in|on|per|every|for|using|with) ${N} ${UNITW}(?: of [a-z]+)?,? (how .+)$`).exec(sents[0]))) { [, , a1, u1, a2, u2, q] = m; }
    else if (sents.length === 2 && (m = new RegExp(`^(?:a|the) recipe (?:uses|calls for|needs|requires) ${N} ${UNITW}(?: of [a-z]+)? (?:for|to make|to bake|makes) ${N} ${UNITW}$`).exec(sents[0]))) { [, a1, u1, a2, u2] = m; q = sents[1]; }
    if (a1 && !/^(?:hours?|minutes?|days?|seconds?)$/.test(u1) === false) return null;
    if (a1 && q) {
      const FREEV = String.raw`(?:[a-z]+)`;
      // how many u1 ... (in|on|for) n u2
      if ((mm = new RegExp(`^how (?:many|much) ${UNITW}(?: of [a-z]+)? (?:does|can|will|would|do|is|are) (?:it|he|she|they|the [a-z]+(?: [a-z]+)?)? ?(?:${FREEV} )?(?:needed |required )?(?:in|on|for|using|with|to make) ${N} ${UNITW}$`).exec(q)) && same(mm[1], u1) && same(mm[3], u2))
        return E(`${a1}/${a2}*${mm[2]}`, `steady rate ${a1} ${u1} per ${a2} ${u2}: ${a1}/${a2} x ${mm[2]}`, ["Assumes a constant rate."]);
      if ((mm = new RegExp(`^how (?:many|much) ${UNITW}(?: of [a-z]+)? (?:are|is) (?:needed|required) (?:for|to make) ${N} ${UNITW}$`).exec(q)) && same(mm[1], u1) && same(mm[3], u2))
        return E(`${a1}/${a2}*${mm[2]}`, `in proportion: ${a1} ${u1} per ${a2} ${u2}, so ${a1}/${a2} x ${mm[2]}`, ["Assumes the amounts stay in proportion."]);
      if ((mm = new RegExp(`^how far (?:can|will|does|would) (?:it|he|she|they) (?:travel|go|drive|run) (?:on|with|using) ${N} ${UNITW}$`).exec(q)) && same(mm[2], u2) && /^(?:miles?|km|kilometers?|kilometres?|meters?|metres?)$/.test(u1))
        return E(`${a1}/${a2}*${mm[1]}`, `steady rate ${a1} ${u1} per ${a2} ${u2}: ${a1}/${a2} x ${mm[1]}`, ["Assumes a constant rate."]);
    }
  }
  return null;
}

// ---------------------------------------------------------------- ratios
const RAT = String.raw`(\d+) ?(?::|to) ?(\d+)(?: ?(?::|to) ?(\d+))?`;
function ratios(sents) {
  let m, mm;
  const E = (math, interp) => result("word-ratio", math, interp, { goal: "evaluate" });
  const head = (s) => s.split(" ")[0];
  const COLLECTIVE = /^(?:students|pupils|people|children|kids|animals|pets|members|players|employees|workers|marbles|balls|beads|cars|books|coins|fruits|flowers|trees|voters|guests|attendees|participants|athletes|items)$/;
  if ((m = new RegExp(`^the ratio of ([a-z]+(?: [a-z]+)?) to ([a-z]+(?: [a-z]+)?)(?: (?:in|at|on) (?:a|the) [a-z]+(?: [a-z]+)?)? is (\\d+) ?(?::|to) ?(\\d+)$`).exec(sents[0]))) {
    const [, A, B, a, b] = m;
    if (head(A) === head(B) || !(+a > 0 && +b > 0)) return null;
    const rest = sents.slice(1).join(", ").replace(/^if /, "");
    if (!(mm = /^there are (\d+) ([a-z]+(?: [a-z]+)?)(?: in (?:the|a|all|total) ?[a-z]*)?(?: in total| altogether| in all)?,? how many ([a-z]+(?: [a-z]+)?) are there(?: in the [a-z]+)?$/.exec(rest))) return null;
    const [, k, X, Y] = mm;
    const which = (w) => (head(w) === head(A) ? "A" : head(w) === head(B) ? "B" : null);
    const want = which(Y);
    if (!want) return null;
    const given = which(X);
    const [wa, wb] = want === "A" ? [a, b] : [b, a];
    if (given === null) {
      if (!COLLECTIVE.test(X) && !/in total|altogether|in all/.test(rest)) return null;
      if (!isInt((+k * +wa) / (+a + +b))) return impossible("the count would not be a whole number"); // a count of people or things must come out whole
      return E(`${k}*${wa}/(${a} + ${b})`, `${Y} are ${wa} of every ${a} + ${b}: ${k} x ${wa}/(${a} + ${b})`);
    }
    if (given === want) return null;
    if (!isInt((+k * +wa) / +wb)) return impossible("the count would not be a whole number");
    return E(`${k}*${wa}/${wb}`, `${Y} : ${X} = ${wa} : ${wb}, so ${k} x ${wa}/${wb}`);
  }
  if (sents.length === 1 && (m = new RegExp(`^(?:divide|split|share) ${N}(?: dollars)? (?:in|into) the ratio ${RAT}$`).exec(sents[0]))) {
    const T = m[1], parts = [m[2], m[3], m[4]].filter(Boolean), s = parts.join(" + ");
    if (parts.some((q) => !(+q > 0))) return null;
    const vars = ["x", "y", "z"].slice(0, parts.length);
    const math = [`${vars.join(" + ")} = ${T}`, ...vars.slice(1).map((v, k) => `${parts[0]}${v} = ${parts[k + 1]}x`)].join(", ");
    return result("word-ratio", math, `parts in the ratio ${parts.join(":")} adding to ${T}: ${math}`);
  }
  if (sents.length === 2 && (m = new RegExp(`^(?:divide|split|share) ${N}(?: dollars)? (?:between|among) ([a-z]+) and ([a-z]+) in the ratio (\\d+) ?(?::|to) ?(\\d+)$`).exec(sents[0]))
    && (mm = /^how much (?:does|will|would) ([a-z]+) (?:get|receive)$/.exec(sents[1]))) {
    const [, T, A, B, a, b] = m;
    if (!(+a > 0 && +b > 0)) return null;
    const k = mm[1] === A ? a : mm[1] === B ? b : null;
    if (!k || A === B) return null;
    return E(`${T}*${k}/(${a} + ${b})`, `${mm[1]} gets ${k} of every ${a} + ${b} parts: ${T} x ${k}/(${a} + ${b})`);
  }
  if (sents.length === 2 && (m = /^a recipe (?:calls for|uses|needs|requires) ([a-z]+) and ([a-z]+) in the ratio (\d+) ?(?::|to) ?(\d+)$/.exec(sents[0]))
    && (mm = new RegExp(`^if you use ${N} ([a-z]+) of ([a-z]+),? how (?:much|many \\2)(?: of)? ([a-z]+) (?:do|will|would|should) you (?:need|use)$`).exec(sents[1]))) {
    const [, A, B, a, b] = m, [, k, , X, Y] = mm;
    if (!((X === A && Y === B) || (X === B && Y === A))) return null;
    const [wx, wy] = X === A ? [a, b] : [b, a];
    return E(`${k}*${wy}/${wx}`, `${Y} : ${X} = ${wy} : ${wx}, so ${k} x ${wy}/${wx}`);
  }
  if (sents.length === 2 && (m = new RegExp(`^the (?:angles|interior angles|measures of the angles|3 angles|4 angles) of a (triangle|quadrilateral) are in the ratio ${RAT}(?: ?(?::|to) ?(\\d+))?$`).exec(sents[0]))
    && (mm = /^(?:find|what is) the (largest|smallest|biggest|greatest|least) angle$/.exec(sents[1]))) {
    const parts = [m[2], m[3], m[4], m[5]].filter(Boolean).map(Number);
    const total = m[1] === "triangle" ? 180 : 360;
    if (parts.length !== (m[1] === "triangle" ? 3 : 4)) return null;
    const k = /larg|bigg|great/.test(mm[1]) ? Math.max(...parts) : Math.min(...parts);
    return E(`${total}*${k}/(${parts.join(" + ")})`, `angles add to ${total} degrees in the ratio ${parts.join(":")}: ${total} x ${k}/(${parts.join(" + ")})`);
  }
  if (sents.length === 3 && (m = /^(?:a|the) map (?:has a )?scale (?:is |of )?(\d+) (cm|mm|in|inch|inches) (?:to|=|represents) (\d+) (km|kilometers|miles|m|meters)$/.exec(sents[0]))
    && (mm = new RegExp(`^(?:2|two) (?:towns|cities|places|points|villages) are ${N} (cm|mm|in|inch|inches) apart on the map$`).exec(sents[1]))
    && /^(?:what is|find|how far is) the (?:actual|real) distance(?: between them)?$/.test(sents[2]) && mm[2] === m[2])
    return E(`${mm[1]}*${m[3]}/${m[1]}`, `every ${m[1]} ${m[2]} on the map is ${m[3]} ${m[4]}: ${mm[1]} x ${m[3]}/${m[1]}, in ${m[4]}`);
  if (sents.length === 1 && (m = /^solve the proportion (.+)$/.exec(sents[0]))) return result("word-ratio", m[1], `solve ${m[1]}`);
  return null;
}

// ---------------------------------------------------------------- two-unknown systems: tickets, coins, heads and legs, purchases
const COIN = { penny: 1, pennie: 1, nickel: 5, dime: 10, quarter: 25, "half dollar": 50 };
const LEGS = { chicken: 2, duck: 2, hen: 2, bird: 2, goose: 2, rooster: 2, turkey: 2, ostrich: 2, cow: 4, pig: 4, horse: 4, goat: 4, sheep: 4, rabbit: 4, dog: 4, cat: 4, lamb: 4, donkey: 4, cattle: 4 };
const WHEELS = { car: 4, motorcycle: 2, bicycle: 2, bike: 2, tricycle: 3, motorbike: 2, scooter: 2, unicycle: 1 };
const tkt = (w) => ({ children: "child", "children's": "child", "child's": "child", kids: "child", kid: "child", adults: "adult", "adult's": "adult", students: "student", "student's": "student", seniors: "senior" }[w] || sing(w));
function systems(sents) {
  let m, mm;
  const text = sents.join(". ");
  // tickets
  if (/\btickets?\b/.test(text)) {
    const st = { price: new Map() };
    const TT = String.raw`([a-z]+(?:'s)?) tickets?`;
    const clauses = [
      [C(`${TT} (?:cost|costs|are|were|sell for|sold for|are priced at|were priced at|cost you) ${N} dollars(?: each)?`), (x, s) => { const k = tkt(x[1]); if (s.price.has(k)) return false; s.price.set(k, +x[2]); }],
      [C(`(?:a total of )?${N} tickets (?:were|are|have been) sold`), (x, s) => set1(s, "count", +x[1])],
      [C(`(?:a|the) [a-z]+(?: [a-z]+)? (?:sold|sells|sold a total of) ${N} tickets`), (x, s) => set1(s, "count", +x[1])],
      [C(`(?:they|we) sold ${N} tickets`), (x, s) => set1(s, "count", +x[1])],
      [C(`(?:for a total of|for|totaling|totalling|bringing in|for total sales of|for a total revenue of) ${N} dollars`), (x, s) => set1(s, "rev", +x[1])],
      [C(`(?:the )?total (?:sales|revenue|receipts|income|amount collected|takings)(?: from (?:the )?tickets)? (?:was|were|is|are|came to|totaled|totalled) ${N} dollars`), (x, s) => set1(s, "rev", +x[1])],
      [C(`(?:they|it|the [a-z]+|we) (?:made|collected|earned|took in|raised|received) ${N} dollars`), (x, s) => set1(s, "rev", +x[1])],
    ];
    let want = null;
    const Q = [
      [/^how many ([a-z]+(?:'s)?) tickets (?:were|did (?:they|it|we|the [a-z]+)) (?:sold|sell)$/, (x) => { want = tkt(x[1]); }],
      [/^how many (?:of each (?:type |kind )?(?:of ticket )?|tickets of each (?:type|kind) )(?:were sold|did (?:they|it|we|the [a-z]+) sell)$/, () => { want = "each"; }],
    ];
    if (!runFacts(sents, clauses, Q, st) || !want || st.price.size !== 2 || st.count === undefined || st.rev === undefined) return null;
    const [[k1, p1], [k2, p2]] = [...st.price];
    if (p1 === p2 || (want !== "each" && want !== k1 && want !== k2)) return null;
    const v1 = k1[0] === k2[0] ? "x" : k1[0], v2 = k1[0] === k2[0] ? "y" : k2[0];
    if ([v1, v2].some((v) => FORBIDDEN_VARS.has(v))) return null;
    const math = `${v1} + ${v2} = ${st.count}, ${p1}${v1} + ${p2}${v2} = ${st.rev}`;
    if (!sensible(math, [v1, v2], COUNT)) return impossible("the numbers of tickets would not be whole and non-negative"); // ticket counts are whole and not negative
    return result("word-system", math, `${v1} = ${k1} tickets, ${v2} = ${k2} tickets; count and money: ${math}${want !== "each" ? ` (the question asks for ${want === k1 ? v1 : v2})` : ""}`);
  }
  // coins and bills
  if (/\b(?:coins|bills)\b/.test(text)) {
    let n, a, b, total, ask;
    const KIND = String.raw`(pennies|nickels|dimes|quarters|half dollars|\d+ dollars bills?|\d+ dollars)`;
    const val = (k) => { const x = /^(\d+) dollars/.exec(k); if (x) return +x[1] * 100; const s = sing(k); return COIN[s] || null; };
    if ((m = new RegExp(`^(?:[a-z]+|(?:a|an|the|his|her|my) [a-z]+(?: [a-z]+)?) (?:has|have|had|holds|contains|saved|collected) ${N} (?:coins|bills),? (?:all )?(?:in |made up of |consisting of |of )?${KIND} and ${KIND}(?: bills)?,? (?:worth|with a total value of|totaling|totalling|that total|adding up to|that add up to|worth a total of) ${N} dollars$`).exec(sents[0]))) [, n, a, b, total] = m;
    if (n && sents.length === 2 && (mm = new RegExp(`^how many ${KIND}(?: bills)? (?:does|do|did) (?:he|she|they|you|i|[a-z]+) have$`).exec(sents[1]))) ask = mm[1];
    if (!n || !ask) return null;
    const va = val(a), vb = val(b.replace(/ bills?$/, "")), vq = val(ask.replace(/ bills?$/, ""));
    if (!va || !vb || va === vb || (vq !== va && vq !== vb)) return null;
    const cents = Math.round(+total * 100);
    const math = `x + y = ${n}, ${va}x + ${vb}y = ${cents}`;
    if (!sensible(math, ["x", "y"], COUNT)) return impossible("the numbers of coins would not be whole and non-negative");
    return result("word-system", math, `x = number of ${a.replace(/^(\d+) dollars/, "$$$1")}, y = number of ${b.replace(/^(\d+) dollars/, "$$$1")}; count and value in cents: ${math} (the question asks for ${vq === va ? "x" : "y"})`);
  }
  // heads and legs / vehicles and wheels
  {
    let A, B;
    const intro = [/^(?:a|the) farmer has (?:some )?([a-z]+) and ([a-z]+)$/, /^(?:in a|on a|at a) [a-z]+(?: [a-z]+)? there are (?:some )?([a-z]+) and ([a-z]+)$/, /^there are (?:some )?([a-z]+) and ([a-z]+) (?:on a|in a|in the|on the|at a) [a-z]+(?: [a-z]+)?$/, /^a (?:farm|yard|barn|field|zoo) has (?:some )?([a-z]+) and ([a-z]+)$/];
    for (const r of intro) if ((m = r.exec(sents[0]))) { [, A, B] = m; break; }
    if (A && sents.length === 3) {
      const a = sing(A), b = sing(B), tab = LEGS[a] && LEGS[b] ? LEGS : WHEELS[a] && WHEELS[b] ? WHEELS : null;
      if (!tab || tab[a] === tab[b]) return null;
      const word = tab === LEGS ? "(?:legs|feet)" : "wheels", count = tab === LEGS ? "(?:heads|animals)" : "(?:vehicles|heads)";
      if (!(mm = new RegExp(`^(?:altogether |in total |together )?there are ${N} ${count} and ${N} ${word}(?: altogether| in total)?$`).exec(sents[1]))) return null;
      const q = new RegExp(`^how many ([a-z]+) are there$|^how many ([a-z]+) does (?:he|she|the farmer) have$`).exec(sents[2]);
      if (!q) return null;
      const W = sing(q[1] || q[2]);
      if (W !== a && W !== b) return null;
      const math = `x + y = ${mm[1]}, ${tab[a]}x + ${tab[b]}y = ${mm[2]}`;
      if (!sensible(math, ["x", "y"], COUNT)) return impossible("the numbers would not be whole and non-negative"); // no negative or fractional animals
      return result("word-system", math, `x = ${A}, y = ${B} (${tab[a]} and ${tab[b]} ${tab === LEGS ? "legs" : "wheels"} each): ${math} (the question asks for ${W === a ? "x" : "y"})`);
    }
  }
  // purchases: 2 pencils and 3 pens cost 13 dollars. 4 pencils and 1 pen cost 11 dollars. how much does a pen cost
  if (sents.length === 3) {
    const rows = [];
    for (const s of sents.slice(0, 2)) {
      if (!(m = new RegExp(`^${N} ([a-z]+) and ${N} ([a-z]+) (?:cost|costs|cost a total of) ${N} dollars$`).exec(s))) return null;
      rows.push([+m[1], sing(m[2]), +m[3], sing(m[4]), +m[5]]);
    }
    const [r1, r2] = rows;
    const A = r1[1], B = r1[3];
    if (A === B) return null;
    const co = (r) => (r[1] === A && r[3] === B ? [r[0], r[2]] : r[1] === B && r[3] === A ? [r[2], r[0]] : null);
    const c1 = co(r1), c2 = co(r2);
    if (!c1 || !c2 || c1[0] * c2[1] === c1[1] * c2[0]) return null;
    if (!(mm = /^how much (?:does|do) (?:a|an|1|one|each) ([a-z]+) cost$|^what is the (?:cost|price) of (?:a|an|1|one) ([a-z]+)$/.exec(sents[2]))) return null;
    const W = sing(mm[1] || mm[2]);
    if (W !== A && W !== B) return null;
    const math = `${c1[0]}x + ${c1[1]}y = ${r1[4]}, ${c2[0]}x + ${c2[1]}y = ${r2[4]}`;
    if (!sensible(math, ["x", "y"], (v) => v > 0)) return impossible("a price would not be positive");
    return result("word-system", math, `x = price of a ${A}, y = price of a ${B}: ${math} (the question asks for ${W === A ? "x" : "y"})`);
  }
  return null;
}

// ---------------------------------------------------------------- angles
function angles(sents) {
  let m, mm;
  const E = (math, interp) => result("word-angles", math, interp, { goal: "evaluate", notes: ["Degrees."] });
  const strip = (s) => s.replace(/ degrees?\b/g, "").replace(/°/g, "");
  const s0 = sents[0];
  if (sents.length === 1 && (m = /^(?:find|what is|calculate) the (complement|supplement) of (?:an? |the )?(\d+(?:\.\d+)?)(?: degrees?)?(?: angle)?$/.exec(s0))) {
    const T = m[1] === "complement" ? 90 : 180;
    if (!(+m[2] < T)) return null;
    return E(`${T} - ${m[2]}`, `${m[1]}s add to ${T} degrees: ${T} - ${m[2]}`);
  }
  // two complementary/supplementary angles with a relation
  if ((m = /^(?:2|two) angles are (complementary|supplementary)(?:,? and (.+))?$/.exec(s0))) {
    const T = m[1] === "complementary" ? 90 : 180;
    // wordsToNumbers turned "one" into "1"; as a subject it is the pronoun, never the number
    const facts = [m[2], ...sents.slice(1)].filter(Boolean).map((f) => f.replace(/^1 (?=is |angle |of )/, "one "));
    const nouns = [];
    for (const p of ["one angle", "one of them", "one of the angles", "one", "the first angle", "the first", "the larger angle", "the larger", "the bigger angle", "the bigger", "the greater angle", "the greater"]) nouns.push(noun(p, "x"));
    for (const p of ["the other angle", "the other", "the second angle", "the second", "the smaller angle", "the smaller", "the other one"]) nouns.push(noun(p, "y"));
    nouns.sort((a, b) => b.words.length - a.words.length);
    const SIZE = /\b(?:larger|smaller|bigger|greater)\b/, ROLE = /\b(?:one|1|other|first|second)\b/;
    const eqs = [`x + y = ${T}`];
    let want = null, sized = false;
    for (const f of facts) {
      if ((mm = /^(?:find|what (?:is|are)) (?:the |both |each )?(smaller|larger|bigger|greater)? ?(?:angles?|of the angles|measures?(?: of the angles)?)$/.exec(f))) { want = mm[1] ? (/small/.test(mm[1]) ? "smaller" : "larger") : "both"; continue; }
      if (SIZE.test(f) && ROLE.test(f)) return null; // "one" and "the larger" could name the same angle or not
      if (SIZE.test(f)) sized = true;
      const e = readEquation(strip(f), nouns, ["x", "y"]);
      if (!e || e.ambiguous) return null;
      eqs.push(e.text);
    }
    if (eqs.length !== 2 || !want) return null;
    const math = eqs.join(", ");
    if (!sensible(math, ["x", "y"], (v) => v > 0 && v < T)) return impossible(`both angles must be between 0 and ${T} degrees`); // both angles must exist
    // with size words in the facts, x is the larger and y the smaller; otherwise both angles are shown and the question picks one
    const ask = want === "both" ? "" : sized ? ` (the question asks for ${want === "larger" ? "x" : "y"})` : ` (the question asks for the ${want} of x and y)`;
    return result("word-angles", math, `x, y the two angles${sized ? " (x the larger)" : ""}, ${m[1]} so they add to ${T} degrees: ${math}${ask}`, { notes: ["Degrees."] });
  }
  if (sents.length === 2 && (m = /^(?:2|two) (?:of the )?angles of a triangle (?:are|measure) (\d+(?:\.\d+)?)(?: degrees)? and (\d+(?:\.\d+)?)(?: degrees)?$/.exec(s0))
    && /^(?:what is|find) the (?:third|remaining|other|missing) angle$/.test(sents[1]) && +m[1] + +m[2] < 180)
    return E(`180 - ${m[1]} - ${m[2]}`, `the angles of a triangle add to 180 degrees: 180 - ${m[1]} - ${m[2]}`);
  if (sents.length === 2 && (m = /^in a right triangle,? (?:one|1) (?:acute )?angle (?:is|measures) (\d+(?:\.\d+)?)(?: degrees)?$/.exec(s0))
    && /^(?:what is|find) the other (?:acute )?angle$/.test(sents[1]) && +m[1] < 90)
    return E(`90 - ${m[1]}`, `the two acute angles of a right triangle add to 90 degrees: 90 - ${m[1]}`);
  if (sents.length === 2 && (m = /^(?:one|1|the vertex) angle of an isosceles triangle (?:is|measures) (\d+(?:\.\d+)?)(?: degrees)?(?:,? and the other (?:2|two)(?: angles)? are equal)?$/.exec(s0))
    && /^(?:what is|find) (?:each of )?the (?:equal|other(?: 2| two)?|remaining(?: 2| two)?|base) angles?$|^what is each of the equal angles$/.test(sents[1])) {
    if (!/other|vertex/.test(s0) || !(+m[1] < 180)) return null; // "one angle" alone could be a base angle
    return E(`(180 - ${m[1]})/2`, `the other two angles are equal and the three add to 180 degrees: (180 - ${m[1]})/2`);
  }
  // angle and its complement / supplement
  if (sents.length === 2 && /^(?:find|what is) the (?:angle|measure of the angle)$/.test(sents[1]) && /\b(?:complement|supplement)\b/.test(s0)) {
    const nouns = [noun("its complement", "(90 - x)", (v) => 90 - v.x), noun("its supplement", "(180 - x)", (v) => 180 - v.x), noun("the measure of an angle", "x"), noun("the measure of the angle", "x"), noun("an angle", "x"), noun("the angle", "x"), noun("the complement of an angle", "(90 - x)", (v) => 90 - v.x), noun("the supplement of an angle", "(180 - x)", (v) => 180 - v.x)];
    nouns.sort((a, b) => b.words.length - a.words.length);
    const e = readEquation(strip(s0), nouns, ["x"]);
    if (!e || e.ambiguous) return null;
    const T = /complement/.test(s0) ? 90 : 180, cond = `0 < x < ${T}`;
    // the angle and its complement/supplement must both be positive: the conditions go into the math
    return result("word-angles", `${e.text}, x > 0, x < ${T}`, `let x be the angle in degrees: ${e.text} (${cond})`, { variable: "x", notes: ["Degrees."] });
  }
  // triangle angles described from the first: in a triangle, the second angle is twice the first and ...
  if ((m = /^in a triangle,? (.+)$/.exec(s0)) && sents.length === 2 && (mm = /^(?:find|what is) the (first|second|third) angle$/.exec(sents[1]))) {
    const nouns = [];
    ["first", "second", "third"].forEach((w, k) => { const v = "abc"[k]; nouns.push(noun(`the ${w} angle`, v), noun(`the ${w}`, v)); });
    nouns.sort((a, b) => b.words.length - a.words.length);
    const eqs = ["a + b + c = 180"];
    for (const p of m[1].split(/,? and (?=the )/)) { const e = readEquation(strip(p), nouns, ["a", "b", "c"]); if (!e || e.ambiguous) return null; eqs.push(e.text); }
    if (eqs.length !== 3) return null;
    const math = eqs.join(", ");
    if (!sensible(math, ["a", "b", "c"], (v) => v > 0)) return impossible("every angle of a triangle must be positive");
    return result("word-angles", math, `a, b, c the first, second and third angles: ${math} (the question asks for ${"abc"["first second third".split(" ").indexOf(mm[1])]})`, { notes: ["Degrees."] });
  }
  // angles given as expressions in x
  if (sents.length === 2 && (m = /^the (?:interior )?angles of a (triangle|quadrilateral|pentagon|hexagon) (?:are|measure) (.+)$/.exec(s0)) && /^(?:find|what is|solve for) (?:the value of )?x$/.test(sents[1])) {
    const parts = strip(m[2]).split(/,? and |, /);
    const n = { triangle: 3, quadrilateral: 4, pentagon: 5, hexagon: 6 }[m[1]];
    if (parts.length !== n || !parts.every((p) => /^[0-9x+\-*() .]+$/.test(p) && /x/.test(p))) return null;
    const math = `${parts.map((p) => (/^[0-9.]*x$/.test(p.trim()) ? p.trim() : `(${p.trim()})`)).join(" + ")} = ${(n - 2) * 180}`;
    const sol = linearSolution(math, ["x"]);
    if (!sol || !parts.every((p) => { try { const v = evalReal(parse(p.trim()), sol); return v > 0 && v < (n - 2) * 180; } catch (_) { return false; } })) return null;
    return result("word-angles", math, `the angles of a ${m[1]} add to ${(n - 2) * 180} degrees: ${math}`, { variable: "x", notes: ["Degrees."] });
  }
  return null;
}

// ---------------------------------------------------------------- entry
const CATEGORIES = [
  ["word-age", ages], ["word-consecutive", consecutiveInts], ["word-two-numbers", twoNumbers], ["word-number", numberSentence],
  ["word-mixture", mixtures], ["word-work", work], ["word-distance", distance], ["word-distance", distanceMore],
  ["word-percent", percents], ["word-percent", percentOf], ["word-interest", interest],
  ["word-geometry", geometry], ["word-geometry", boxVolume], ["word-probability", probability], ["word-rate", unitRates], ["word-ratio", ratios],
  ["word-system", systems], ["word-angles", angles],
];
export function wordPatterns({ wordsToNumbers }) {
  return [{
    id: "word-problem", re: /^(.{12,})$/s,
    build: (m) => {
      const t = normaliseWords(m[1], wordsToNumbers);
      const sents = sentencesOf(t);
      if (!sents.length || sents.length > 8) return null;
      for (const [, fn] of CATEGORIES) {
        let r = null;
        try { r = fn(sents, t); } catch (e) { if (typeof process !== "undefined" && process.env && process.env.QV_WORDS_DEBUG) console.error(e); r = null; }
        if (r && (r.math || r.refuse)) return r;
      }
      return null;
    },
  }];
}
