// "Prove that ..." phrasings -> proof commands (see proof.js). Only statements with a mechanical
// certificate are translated to a checking command; other general theorems become proofrequest(...),
// which refuses with the reason. Statements with no English words (plain formulas such as
// sin(x)^2 + cos(x)^2 = 1) that are not polynomial/rational are left to the ordinary engine.

import { parseDetailed } from "../parse.js";
import { formulaText } from "./lang-logic.js";
import { isRationalExpr } from "./proof.js";

const INTS = String.raw`(?:positive\s+|non-?negative\s+|natural\s+)?(?:integers?|natural numbers?|whole numbers?|numbers?)`;
const REL = (s) => s.replace(/≤|=<|⩽/g, "<=").replace(/≥|=>|⩾/g, ">=").replace(/≠/g, "!=");
const vcode = (s) => `vlabel(${[...s.slice(0, 60)].map((c) => c.charCodeAt(0)).join(", ")})`;
function parses(s) { try { return parseDetailed(s).node; } catch (_) { return null; } }
function singleVar(s) {
  const t = parses(s);
  if (!t) return null;
  const vs = [...freeSyms(t)];
  return vs.length === 1 ? vs[0] : null;
}
function freeSyms(u, out = new Set()) { if (u.k === "sym") out.add(u.name); (u.args || []).forEach((a) => freeSyms(a, out)); return out; }
const MATHWORDS = new Set(["sin", "cos", "tan", "sec", "csc", "cot", "log", "exp", "sqrt", "abs", "sinh", "cosh", "tanh", "arcsin", "arccos", "arctan", "floor", "ceil", "mod", "gcd", "lcm", "max", "min", "det", "sum", "for", "all", "and", "real", "reals", "every", "any", "each"]);
function hasEnglish(s) { return (s.match(/[A-Za-z]{3,}/g) || []).some((w) => !MATHWORDS.has(w.toLowerCase())); }

const MATH_TOPIC = /\b(?:primes?|irrational|rational|integers?|numbers?|groups?|rings?|fields?|subgroups?|cyclic|abelian|isomorphic|graphs?|trees?|vertices|edges|planar|matri(?:x|ces)|determinant|eigenvalues?|polynomials?|roots?|functions?|continuous|differentiable|bounded|converges?|convergent|diverges?|series|sequences?|limits?|sets?|countabl[ey]|uncountabl[ey]|infinite(?:ly)?|finite|divisible|divides|odd|even|squares?|cubes?|triangles?|angles?|circles?|theorem|lemma|conjecture|inequality|identity|equation)\b/i;
const NAMED_SUMS = [
  [/^(?:odd\s+(?:positive\s+)?(?:numbers|integers|natural numbers))$/i, "2k - 1"],
  [/^(?:even\s+(?:positive\s+)?(?:numbers|integers|natural numbers))$/i, "2k"],
  [/^(?:positive\s+integers|natural numbers|integers|numbers|counting numbers)$/i, "k"],
  [/^(?:perfect\s+)?squares$/i, "k^2"],
  [/^(?:perfect\s+)?cubes$/i, "k^3"],
];

export function recogniseProof(text) {
  // "verify that ..." is left to the ordinary engine (identity checks); only proof requests here
  let m = text.match(/^(?:prove|show|demonstrate)(?:\s+that)?\s+(.+)$/i);
  if (!m) return null;
  const s = REL(m[1].trim());
  let r;
  // divisibility
  if ((r = s.match(new RegExp(String.raw`^(.+?)\s+is\s+(?:always\s+)?divisible\s+by\s+(\d+)(?:\s+for\s+(?:every|all|each|any)\s+(?:${INTS}\s*)?([a-z])?)?$`, "i")))
    || (r = s.match(new RegExp(String.raw`^(\d+)\s+(?:divides|\|)\s+(.+?)(?:\s+for\s+(?:every|all|each|any)\s+(?:${INTS}\s*)?([a-z])?)?$`, "i")))) {
    const [expr, mod] = /^\d+$/.test(r[1]) ? [r[2], r[1]] : [r[1], r[2]];
    const v = r[3] || singleVar(expr);
    if (!v || !parses(expr)) return null;
    return { math: `provedivisible(${expr}, ${v}, ${mod})`, interpretation: `Prove that ${mod} divides ${expr} for every integer ${v}` };
  }
  // is prime for all n >= a
  if ((r = s.match(new RegExp(String.raw`^(.+?)\s+is\s+(?:always\s+)?(?:a\s+)?prime(?:\s+number)?\s+for\s+(?:all|every|each)\s+(?:(${INTS})\s+)?([a-z])(?:\s*(>=|>)\s*(-?\d+))?$`, "i")))) {
    const lo = r[4] ? (r[4] === ">" ? String(Number(r[5]) + 1) : r[5]) : r[2] && /non-?negative/i.test(r[2]) ? "0" : r[2] && /positive|natural/i.test(r[2]) ? "1" : null;
    if (lo === null || !parses(r[1])) return null;
    return { math: `provealwaysprime(${r[1]}, ${r[3]}, ${lo})`, interpretation: `Is ${r[1]} prime for every ${r[3]} >= ${lo}?` };
  }
  // finite universe: for all x in {..}, rel
  if ((r = s.match(/^for\s+(?:all|every|each)\s+([a-z])\s+in\s+\{([^{}]+)\}\s*,?\s*(.+)$/i)) || (r = s.match(/^(.+?)\s+for\s+(?:all|every|each)\s+([a-z])\s+in\s+\{([^{}]+)\}$/i))) {
    const [x, set, rel] = r[1].length === 1 ? [r[1], r[2], r[3]] : [r[2], r[3], r[1]];
    const rng = set.match(/^\s*(-?\d+)\s*,\s*(?:\.\.\.|…)\s*,\s*(-?\d+)\s*$/) || set.match(/^\s*(-?\d+)\s*\.\.\s*(-?\d+)\s*$/);
    const vals = rng ? Array.from({ length: Math.max(0, Number(rng[2]) - Number(rng[1]) + 1) }, (_, i) => String(Number(rng[1]) + i)) : set.split(",").map((t) => t.trim());
    if (!vals.length || vals.length > 100000 || !vals.every((v) => /^-?\d+(?:\/\d+)?$/.test(v)) || !/[<>=]/.test(rel)) return null;
    return { math: `provefinite(${rel}, ${x}, [${vals.join(", ")}])`, interpretation: `Check ${rel} for every ${x} in the set` };
  }
  // sums
  if ((r = s.match(/^the\s+sum\s+of\s+the\s+first\s+([a-z])\s+(.+?)\s+(?:is|equals|=)\s+(.+)$/i))) {
    const hit = NAMED_SUMS.find(([re]) => re.test(r[2].trim()));
    if (!hit || !parses(r[3])) return null;
    return { math: `provesum(${hit[1]}, k, ${r[1]}, ${r[3]}, 1)`, interpretation: `Prove that the sum of the first ${r[1]} ${r[2]} is ${r[3]}` };
  }
  if ((r = s.match(/^the\s+sum\s+of\s+(.+?)\s+for\s+([a-z])\s*(?:=|from)\s*(-?\d+)\s+(?:to|\.\.)\s+([a-z])\s+(?:is|equals|=)\s+(.+)$/i))) {
    if (!parses(r[1]) || !parses(r[5])) return null;
    return { math: `provesum(${r[1]}, ${r[2]}, ${r[4]}, ${r[5]}, ${r[3]})`, interpretation: `Prove that the sum of ${r[1]} for ${r[2]} = ${r[3]} to ${r[4]} is ${r[5]}` };
  }
  if ((r = s.match(/^(.+?)\s*\+\s*(?:\.\.\.|…|⋯|\.\s\.\s\.)\s*\+\s*(.+?)\s*=\s*(.+)$/))) {
    const first = r[1].split("+").map((t) => t.trim());
    const last = r[2].trim(), F = r[3].trim();
    const v = singleVar(last);
    if (!v || !first.every((t) => /^-?\d+(?:\s*\^\s*\d+)?$/.test(t)) || !parses(F)) return null;
    // the listed terms as numbers (2^2 -> 4 is evaluated by the parser's arithmetic in the handler)
    return { math: `provesum(${last}, ${v}, ${v}, ${F}, [${first.join(", ")}])`, interpretation: `Prove that ${r[1]} + ... + ${last} = ${F}` };
  }
  // logic
  if ((r = s.match(/^(.+?)\s+is\s+(?:logically\s+)?equivalent\s+to\s+(.+)$/i))) {
    const a = formulaText(r[1]), b = formulaText(r[2]);
    if (a && b) return { math: `proveequiv(${a}, ${b})`, interpretation: `Prove that ${r[1]} is equivalent to ${r[2]}` };
  }
  if ((r = s.match(/^(.+?)\s+is\s+a\s+tautology$/i))) {
    const a = formulaText(r[1]);
    if (a) return { math: `proveequiv(${a}, 1)`, interpretation: `Prove that ${r[1]} is a tautology` };
  }
  // inequalities over a range of integers: bounded search
  if ((r = s.match(new RegExp(String.raw`^(.+?)\s+for\s+(?:all\s+|every\s+|each\s+)?(?:(${INTS})\s+)?([a-z])\s*(>=|>)\s*(-?\d+)$`, "i")))
    || (r = s.match(new RegExp(String.raw`^(.+?)\s+for\s+(?:all|every|each)\s+(${INTS})\s+([a-z])$`, "i")))) {
    const rel = r[1];
    let lo = null;
    if (r[4]) lo = r[4] === ">" ? String(Number(r[5]) + 1) : r[5];
    else if (/non-?negative/i.test(r[2] || "")) lo = "0";
    else if (/positive|natural/i.test(r[2] || "")) lo = "1";
    if (lo === null || !/[<>]|!=/.test(rel) || !parses(rel)) return null;
    return { math: `provebound(${rel}, ${r[3]}, ${lo})`, interpretation: `Check ${rel} for ${r[3]} >= ${lo}` };
  }
  // identities
  if (!hasEnglish(s) && (s.match(/=/g) || []).length === 1 && !/[<>!]/.test(s)) {
    const [L, R] = s.split("=").map((t) => t.trim());
    const l = parses(L), rr = parses(R);
    if (l && rr && isRationalExpr(l) && isRationalExpr(rr)) return { math: `proveidentity(${L}, ${R})`, interpretation: `Prove the identity ${L} = ${R}` };
    return null;
  }
  // a general mathematical theorem: refused with the reason (non-mathematical text is not claimed)
  if (hasEnglish(s) && MATH_TOPIC.test(s)) return { math: `proofrequest(${vcode(s)})`, interpretation: `Prove that ${s}` };
  return null;
}
