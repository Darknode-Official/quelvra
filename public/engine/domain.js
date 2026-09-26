// Quelvra domain and assumption module.
//
//   inferDomain(tree, {ctx})            -> { conditions: [{ rel, reason, sub }], rels: [node], empty }
//   domainConditions(tree, {ctx})       -> [rel nodes]           (just the relations)
//   equationConditions(eq, {ctx})       -> domain of both sides + "a square root is nonnegative" conditions
//   checkPoint(conditions, env, {ctx})  -> { ok: true | false | null, results, violated, undecided, method }
//   normalizeConditions(list, ctx)      -> [rel nodes] (decided-true dropped) or null when one is false
//   decideRel(cond, ctx)                -> true | false | null
//   signUnder(u, ctx)                   -> 1 | -1 | 0 | "nn" | "np" | "nz" | null
//   parseAssumptions(input)             -> Map name -> Set of tags   (see parseAssumptionsDetailed)
//   deriveTags(tags)                    -> closed Set (x > 0 => positive, nonnegative, nonzero, real)
//   makeAssumeCtx(assumptions, opts)    -> simplify ctx with .assume (and .bounds for interval facts)
//   simplifyUnder(tree, assumptions)    -> simplifyFull(tree) under those assumptions
//
// Conditions are relation trees (rel / and / not / bool nodes, plus the predicate fn("isInteger", u)).
// Domain inference works on the ORIGINAL tree: simplification can hide a restriction (x/x -> 1).

import * as N from "./num.js";
import * as X from "./expr.js";
import { simplify, makeCtx } from "./simplify.js";
import { parse } from "./parse.js";
import { toText } from "./print.js";
import { simplifyFull, evalNumeric } from "./rules.js";

const { ZERO, ONE, NEG_ONE, TRUE, FALSE, UNDEF, I, E, PI } = X;

// ---------------- small helpers ----------------
function budgetErr(msg) {
  const e = new Error("Quelvra: " + msg);
  e.code = "BUDGET";
  return e;
}
const freshCtx = (ctx) => ctx || makeCtx();
const plainCtx = (ctx) => ({ ...freshCtx(ctx), conditions: null });
// simplify that never escapes with a JS stack overflow (a foundation bug makes some inputs recurse forever)
export function safeSimplify(u, ctx) {
  try {
    return simplify(u, plainCtx(ctx));
  } catch (e) {
    if (e instanceof RangeError) return null;
    throw e;
  }
}
const containsNode = (u, t) => X.contains(u, t);

// ---------------- tags / assumptions ----------------
const IMPLIES = {
  positive: ["positive", "nonnegative", "nonzero", "real"],
  negative: ["negative", "nonpositive", "nonzero", "real"],
  nonnegative: ["nonnegative", "real"],
  nonpositive: ["nonpositive", "real"],
  nonzero: ["nonzero"],
  integer: ["integer", "rational", "real"],
  even: ["even", "integer", "rational", "real"],
  odd: ["odd", "integer", "rational", "real", "nonzero"],
  rational: ["rational", "real"],
  real: ["real"],
  natural: ["integer", "rational", "real", "nonnegative"],
  complex: ["complex"],
};
export function deriveTags(tags) {
  const out = new Set();
  const todo = [...tags];
  let guard = 0;
  while (todo.length) {
    if (++guard > 1000) throw budgetErr("tag derivation");
    const t = todo.pop();
    if (out.has(t)) continue;
    out.add(t);
    for (const u of IMPLIES[t] || []) if (!out.has(u)) todo.push(u);
  }
  if (out.has("nonnegative") && out.has("nonzero")) out.add("positive");
  if (out.has("nonpositive") && out.has("nonzero")) out.add("negative");
  if (out.has("positive") || out.has("negative")) { out.add("nonzero"); out.add("real"); }
  return out;
}

const WORD_TAGS = {
  positive: ["positive"], negative: ["negative"], nonnegative: ["nonnegative"], "non-negative": ["nonnegative"],
  nonpositive: ["nonpositive"], "non-positive": ["nonpositive"], nonzero: ["nonzero"], "non-zero": ["nonzero"],
  integer: ["integer"], int: ["integer"], real: ["real"], even: ["even"], odd: ["odd"], rational: ["rational"],
  natural: ["natural"], complex: ["complex"],
};
const SET_TAGS = { Z: ["integer"], "ℤ": ["integer"], R: ["real"], "ℝ": ["real"], N: ["natural"], "ℕ": ["natural"], Q: ["rational"], "ℚ": ["rational"], C: ["complex"], "ℂ": ["complex"] };

function addTags(map, name, tags) {
  const prev = map.get(name) || new Set();
  map.set(name, deriveTags([...prev, ...tags]));
}
function mergeBound(bounds, name, side, value, open) {
  const b = bounds.get(name) || { lo: null, loOpen: false, hi: null, hiOpen: false };
  if (side === "lo") {
    if (!b.lo || constSign(X.sub(value, b.lo)) === 1 || (constSign(X.sub(value, b.lo)) === 0 && open)) { b.lo = value; b.loOpen = open; }
  } else if (!b.hi || constSign(X.sub(value, b.hi)) === -1 || (constSign(X.sub(value, b.hi)) === 0 && open)) { b.hi = value; b.hiOpen = open; }
  bounds.set(name, b);
}
// A relation "sym op constant" (either orientation) becomes tags + bounds.
function relToFacts(r, assume, bounds) {
  let [l, rr] = r.args;
  let op = r.op;
  const flip = { "<": ">", ">": "<", "<=": ">=", ">=": "<=", "!=": "!=" };
  if (l.k !== "sym" && rr.k === "sym") { [l, rr] = [rr, l]; op = flip[op]; }
  if (l.k !== "sym" || X.freeSymbols(rr).size) return false;
  const c = safeSimplify(rr);
  if (!c) return false;
  const s = constSign(c);
  const name = l.name;
  const tags = ["real"];
  if (op === ">") { mergeBound(bounds, name, "lo", c, true); if (s === 0 || s === 1) tags.push("positive"); }
  else if (op === ">=") { mergeBound(bounds, name, "lo", c, false); if (s === 1) tags.push("positive"); else if (s === 0) tags.push("nonnegative"); }
  else if (op === "<") { mergeBound(bounds, name, "hi", c, true); if (s === 0 || s === -1) tags.push("negative"); }
  else if (op === "<=") { mergeBound(bounds, name, "hi", c, false); if (s === -1) tags.push("negative"); else if (s === 0) tags.push("nonpositive"); }
  else if (op === "!=") { if (s === 0) tags.push("nonzero"); }
  else return false;
  addTags(assume, name, tags);
  return true;
}

// Parse assumption statements: "x > 0", "n integer", "n is an even integer", "a != 0",
// "-pi/2 <= t <= pi/2", "k in Z", "x real". Several may be joined by "," ";" or "and".
export function parseAssumptionsDetailed(input) {
  const assume = new Map();
  const bounds = new Map();
  const relations = [];
  const unparsed = [];
  if (input instanceof Map) {
    for (const [k, v] of input) addTags(assume, k, v instanceof Set ? [...v] : [].concat(v));
    return { assume, bounds, relations, unparsed };
  }
  const list = Array.isArray(input) ? input : input == null ? [] : typeof input === "string" ? [input] : null;
  if (!list) {
    for (const [k, v] of Object.entries(input)) addTags(assume, k, [].concat(v));
    return { assume, bounds, relations, unparsed };
  }
  const parts = [];
  for (const item of list) {
    if (typeof item !== "string") { if (item && item.k) parts.push(item); continue; }
    for (const p of item.split(/[,;]|\band\b/)) if (p.trim()) parts.push(p.trim());
  }
  for (const p of parts) {
    if (typeof p !== "string") { handleNode(p); continue; }
    let m = p.match(/^([A-Za-z][A-Za-z0-9_]*)\s+(?:is\s+)?(?:an?\s+)?((?:[A-Za-z-]+\s*)+)$/i);
    if (m) {
      const words = m[2].trim().toLowerCase().split(/\s+/).filter((w) => w !== "number");
      if (words.length && words.every((w) => WORD_TAGS[w])) {
        addTags(assume, m[1], words.flatMap((w) => WORD_TAGS[w]));
        continue;
      }
    }
    m = p.match(/^([A-Za-z][A-Za-z0-9_]*)\s*(?:in|∈)\s*(\S+)$/);
    if (m && SET_TAGS[m[2]]) { addTags(assume, m[1], SET_TAGS[m[2]]); continue; }
    let node;
    try { node = parse(p); } catch (_) { unparsed.push(p); continue; }
    if (!handleNode(node)) unparsed.push(p);
  }
  function handleNode(node) {
    if (node.k === "and") return node.args.map(handleNode).every(Boolean);
    if (node.k === "rel") {
      relations.push(node);
      return relToFacts(node, assume, bounds);
    }
    return false;
  }
  return { assume, bounds, relations, unparsed };
}
export const parseAssumptions = (input) => parseAssumptionsDetailed(input).assume;

export function makeAssumeCtx(assumptions, opts = {}) {
  let info;
  if (assumptions && assumptions.domain && assumptions.assume && assumptions.budget) return assumptions; // already a ctx
  info = parseAssumptionsDetailed(assumptions || []);
  const ctx = makeCtx({ domain: opts.domain || "real", assume: info.assume, conditions: opts.conditions || null, budget: opts.budget });
  ctx.bounds = info.bounds;
  ctx.relations = info.relations;
  return ctx;
}

// ---------------- sign knowledge (ctx-aware) ----------------
// The canonicaliser's exported signOf reads the ctx only during a simplify() call, so a ctx-aware
// version lives here. Returns 1, -1, 0, "nn" (>= 0), "np" (<= 0), "nz" (nonzero, sign unknown), null.
function tagsOf(ctx, name) {
  return (ctx && ctx.assume && ctx.assume.get(name)) || null;
}
export function signUnder(u, ctx, depth = 0) {
  if (depth > 200) return null;
  const real = !ctx || ctx.domain !== "complex";
  switch (u.k) {
    case "num": return N.sign(u.v);
    case "const": return u.name === "pi" || u.name === "e" || u.name === "oo" ? 1 : null;
    case "sym": {
      const t = tagsOf(ctx, u.name);
      if (t) {
        if (t.has("positive")) return 1;
        if (t.has("negative")) return -1;
        if (t.has("nonnegative")) return "nn";
        if (t.has("nonpositive")) return "np";
        if (t.has("nonzero")) return "nz";
      }
      const b = ctx && ctx.bounds && ctx.bounds.get(u.name);
      if (b) {
        if (b.lo) { const s = constSign(b.lo); if (s === 1 || (s === 0 && b.loOpen)) return 1; if (s === 0) return "nn"; }
        if (b.hi) { const s = constSign(b.hi); if (s === -1 || (s === 0 && b.hiOpen)) return -1; if (s === 0) return "np"; }
      }
      return null;
    }
    case "add": {
      let pos = 0, neg = 0, nn = 0, np = 0;
      for (const a of u.args) {
        const t = signUnder(a, ctx, depth + 1);
        if (t === null || t === "nz") return signByBounds(u, ctx) ?? signFromRange(u, ctx);
        if (t === 1) pos++; else if (t === -1) neg++; else if (t === "nn") nn++; else if (t === "np") np++;
      }
      if (!neg && !np && pos) return 1;
      if (!pos && !nn && neg) return -1;
      if (!neg && !np) return "nn";
      if (!pos && !nn) return "np";
      return signByBounds(u, ctx) ?? signFromRange(u, ctx);
    }
    case "mul": {
      let s = 1, weak = false, nzUnknown = false;
      for (const a of u.args) {
        const t = signUnder(a, ctx, depth + 1);
        if (t === 0) return 0;
        if (t === null) return null;
        if (t === "nz") nzUnknown = true;
        else if (t === "nn") weak = true;
        else if (t === "np") { weak = true; s = -s; }
        else s *= t;
      }
      if (nzUnknown) return weak ? null : "nz";
      return weak ? (s > 0 ? "nn" : "np") : s;
    }
    case "pow": {
      const [b, e] = u.args;
      const sb = signUnder(b, ctx, depth + 1);
      if (b === E) return 1;
      if (sb === 1) return 1;
      if (e.k === "num") {
        const ev = e.v;
        if (ev.d === 1n) {
          const even = ev.n % 2n === 0n;
          if (sb === 0) return ev.n > 0n ? 0 : null;
          if (even) return sb === -1 || sb === "nz" ? 1 : real ? (ev.n > 0n ? "nn" : 1) : null;
          // odd integer power keeps the sign (negative powers: when defined)
          if (sb === -1) return -1;
          if (sb === "nz") return "nz";
          if (sb === "nn") return ev.n > 0n ? "nn" : 1;
          if (sb === "np") return ev.n > 0n ? "np" : -1;
          return null;
        }
        if (real) {
          if (ev.d % 2n === 0n) return ev.n > 0n ? (sb === "nz" ? 1 : "nn") : 1; // even root (when defined)
          // odd root keeps sign; even numerator gives >= 0
          if (ev.n % 2n === 0n) return sb === -1 || sb === "nz" ? 1 : "nn";
          if (sb === -1) return -1;
          if (sb === "nz") return "nz";
          if (sb === "nn") return ev.n > 0n ? "nn" : 1;
          if (sb === "np") return ev.n > 0n ? "np" : -1;
        }
        return null;
      }
      return null;
    }
    case "fn": {
      const a = u.args[0];
      const sa = a ? signUnder(a, ctx, depth + 1) : null;
      switch (u.name) {
        case "abs": return sa === 0 ? 0 : sa === 1 || sa === -1 || sa === "nz" ? 1 : "nn";
        case "exp": case "cosh": return 1;
        case "sqrt": return sa === 1 ? 1 : "nn";
        case "sinh": case "tanh": case "atan": case "asinh": case "cbrt": case "asin": case "atanh": case "sign": return sa;
        case "acos": return "nn";
        case "factorial": return sa === 1 || sa === 0 || sa === "nn" ? 1 : null;
        default: return null;
      }
    }
    default: return null;
  }
}

// ---------------- exact interval arithmetic (range reasoning) ----------------
// An interval is { lo, hi, loOpen, hiOpen } with Rational endpoints, null meaning infinite.
const FULL = { lo: null, hi: null, loOpen: true, hiOpen: true };
const ivConst = (q) => ({ lo: q, hi: q, loOpen: false, hiOpen: false });
function ivAdd(a, b) {
  return {
    lo: a.lo && b.lo ? N.add(a.lo, b.lo) : null, loOpen: a.loOpen || b.loOpen,
    hi: a.hi && b.hi ? N.add(a.hi, b.hi) : null, hiOpen: a.hiOpen || b.hiOpen,
  };
}
function ivScale(a, k) {
  if (N.isZero(k)) return ivConst(N.ZERO);
  const lo = a.lo && N.mul(a.lo, k), hi = a.hi && N.mul(a.hi, k);
  return N.isPos(k) ? { lo, hi, loOpen: a.loOpen, hiOpen: a.hiOpen } : { lo: hi, hi: lo, loOpen: a.hiOpen, hiOpen: a.loOpen };
}
function ivMul(a, b) {
  // only for bounded intervals; otherwise use sign information
  if (!a.lo || !a.hi || !b.lo || !b.hi) {
    const pa = a.lo && !N.isNeg(a.lo), pb = b.lo && !N.isNeg(b.lo);
    if (pa && pb) return { lo: N.mul(a.lo, b.lo), hi: null, loOpen: a.loOpen || b.loOpen, hiOpen: true };
    return FULL;
  }
  const ps = [[a.lo, a.loOpen, b.lo, b.loOpen], [a.lo, a.loOpen, b.hi, b.hiOpen], [a.hi, a.hiOpen, b.lo, b.loOpen], [a.hi, a.hiOpen, b.hi, b.hiOpen]]
    .map(([x, xo, y, yo]) => [N.mul(x, y), xo || yo]);
  let lo = ps[0], hi = ps[0];
  for (const p of ps) {
    if (N.lt(p[0], lo[0]) || (N.eq(p[0], lo[0]) && !p[1])) lo = p;
    if (N.lt(hi[0], p[0]) || (N.eq(p[0], hi[0]) && !p[1])) hi = p;
  }
  return { lo: lo[0], hi: hi[0], loOpen: lo[1], hiOpen: hi[1] };
}
export function rangeOf(u, ctx, depth = 0) {
  if (depth > 60) return FULL;
  switch (u.k) {
    case "num": return ivConst(u.v);
    case "const": return u.name === "pi" ? { lo: N.Q(314, 100), hi: N.Q(315, 100), loOpen: false, hiOpen: false } : u.name === "e" ? { lo: N.Q(271, 100), hi: N.Q(272, 100), loOpen: false, hiOpen: false } : FULL;
    case "sym": {
      const t = tagsOf(ctx, u.name);
      let iv = FULL;
      if (t) {
        if (t.has("positive")) iv = { ...iv, lo: N.ZERO, loOpen: true };
        else if (t.has("nonnegative")) iv = { ...iv, lo: N.ZERO, loOpen: false };
        if (t.has("negative")) iv = { ...iv, hi: N.ZERO, hiOpen: true };
        else if (t.has("nonpositive")) iv = { ...iv, hi: N.ZERO, hiOpen: false };
      }
      const b = ctx && ctx.bounds && ctx.bounds.get(u.name);
      if (b) {
        if (b.lo && b.lo.k === "num" && (!iv.lo || !N.lt(b.lo.v, iv.lo))) iv = { ...iv, lo: b.lo.v, loOpen: b.loOpen };
        if (b.hi && b.hi.k === "num" && (!iv.hi || !N.lt(iv.hi, b.hi.v))) iv = { ...iv, hi: b.hi.v, hiOpen: b.hiOpen };
      }
      return iv;
    }
    case "add": return u.args.reduce((acc, a) => ivAdd(acc, rangeOf(a, ctx, depth + 1)), ivConst(N.ZERO));
    case "mul": {
      let acc = ivConst(N.ONE);
      for (const a of u.args) acc = a.k === "num" ? ivScale(acc, a.v) : ivMul(acc, rangeOf(a, ctx, depth + 1));
      return acc;
    }
    case "pow": {
      const [b, e] = u.args;
      if (e.k === "num" && e.v.d === 1n && e.v.n > 0n && e.v.n <= 8n) {
        const rb = rangeOf(b, ctx, depth + 1);
        const even = e.v.n % 2n === 0n;
        let acc = ivConst(N.ONE);
        for (let i = 0n; i < e.v.n; i++) acc = ivMul(acc, rb);
        if (even && (!acc.lo || N.isNeg(acc.lo))) return { lo: N.ZERO, loOpen: false, hi: acc.hi && rb.lo && rb.hi ? acc.hi : null, hiOpen: acc.hiOpen };
        return acc;
      }
      if (e.k === "num" && e.v.d % 2n === 0n && N.isPos(e.v)) return { lo: N.ZERO, loOpen: false, hi: null, hiOpen: true };
      if (b === E) return { lo: N.ZERO, loOpen: true, hi: null, hiOpen: true };
      return FULL;
    }
    case "fn":
      if (u.name === "sin" || u.name === "cos") return { lo: N.NEG_ONE, hi: N.ONE, loOpen: false, hiOpen: false };
      if (u.name === "abs") return { lo: N.ZERO, loOpen: false, hi: null, hiOpen: true };
      if (u.name === "exp" || u.name === "cosh") return { lo: u.name === "exp" ? N.ZERO : N.ONE, loOpen: u.name === "exp", hi: null, hiOpen: true };
      if (u.name === "atan") return { lo: N.Q(-16, 10), hi: N.Q(16, 10), loOpen: false, hiOpen: false };
      if (u.name === "tanh") return { lo: N.NEG_ONE, hi: N.ONE, loOpen: true, hiOpen: true };
      return FULL;
    default: return FULL;
  }
}
function signFromRange(u, ctx) {
  const r = rangeOf(u, ctx);
  if (r.lo && (N.isPos(r.lo) || (N.isZero(r.lo) && r.loOpen))) return 1;
  if (r.hi && (N.isNeg(r.hi) || (N.isZero(r.hi) && r.hiOpen))) return -1;
  if (r.lo && N.isZero(r.lo)) return "nn";
  if (r.hi && N.isZero(r.hi)) return "np";
  return null;
}

// a x + b with x known to lie in [lo, hi] (assumption bounds)
function signByBounds(u, ctx) {
  if (!ctx || !ctx.bounds || !ctx.bounds.size) return null;
  const lin = linearIn(u);
  if (!lin) return null;
  const [x, a, b] = lin;
  const bd = ctx.bounds.get(x.name);
  if (!bd) return null;
  const at = (v) => constSign(X.add(X.mul(X.num(a), v), b));
  const up = N.isPos(a);
  const low = up ? bd.lo : bd.hi, lowOpen = up ? bd.loOpen : bd.hiOpen; // end giving the smallest value
  const high = up ? bd.hi : bd.lo, highOpen = up ? bd.hiOpen : bd.loOpen;
  if (low) { const s = at(low); if (s === 1 || (s === 0 && lowOpen)) return 1; if (s === 0) return "nn"; }
  if (high) { const s = at(high); if (s === -1 || (s === 0 && highOpen)) return -1; if (s === 0) return "np"; }
  return null;
}

// Sign of a constant (symbol-free) expression: exact first, then high-precision / double numerics.
export function constSign(u) {
  if (X.freeSymbols(u).size) return null;
  const v = safeSimplify(u);
  if (!v || v === UNDEF) return null;
  if (v.k === "num") return N.sign(v.v);
  const s = signUnder(v, null);
  if (s === 1 || s === -1 || s === 0) return s;
  const hp = hpSign(v);
  if (hp !== null) return hp;
  const f = evalNumeric(v, {}, { mode: "real" });
  if (f && Math.abs(f.re) > 1e-12) return Math.sign(f.re);
  return null;
}

// ---------------- high-precision fixed-point evaluation (algebraic numbers, pi, e) ----------------
const HP_DIGITS = 60n;
const HP_S = 10n ** HP_DIGITS;
const HP_PI = 3141592653589793238462643383279502884197169399375105820974944n; // 60 digits after the point
const HP_E = 2718281828459045235360287471352662497757247093699959574966967n;
function hpEval(u, depth = 0) {
  if (depth > 60) throw budgetErr("hp depth");
  switch (u.k) {
    case "num": return (u.v.n * HP_S) / u.v.d;
    case "const":
      if (u.name === "pi") return HP_PI;
      if (u.name === "e") return HP_E;
      throw new Error("hp: unsupported constant");
    case "add": return u.args.reduce((s, a) => s + hpEval(a, depth + 1), 0n);
    case "mul": return u.args.reduce((s, a) => (s * hpEval(a, depth + 1)) / HP_S, HP_S);
    case "pow": {
      const [b, e] = u.args;
      if (e.k !== "num") throw new Error("hp: symbolic exponent");
      let v = hpEval(b, depth + 1);
      const p = e.v.n, q = e.v.d;
      if (q > 1n) {
        if (q > 64n) throw new Error("hp: root too large");
        if (v < 0n) {
          if (q % 2n === 0n) throw new Error("hp: even root of negative");
          v = -N.iroot(-v * HP_S ** (q - 1n), q)[0];
        } else v = N.iroot(v * HP_S ** (q - 1n), q)[0];
      }
      let k = p < 0n ? -p : p;
      if (k > 400n) throw new Error("hp: power too large");
      let r = HP_S;
      for (let i = 0n; i < k; i++) r = (r * v) / HP_S;
      if (p < 0n) {
        if (r === 0n) throw new Error("hp: division by zero");
        r = (HP_S * HP_S) / r;
      }
      return r;
    }
    case "fn":
      if (u.name === "abs") { const v = hpEval(u.args[0], depth + 1); return v < 0n ? -v : v; }
      throw new Error("hp: unsupported function");
    default: throw new Error("hp: unsupported node");
  }
}
function hpSign(u) {
  try {
    const v = hpEval(u);
    const tiny = 10n ** 20n; // |value| > 1e-40 is decisive at 60 digits
    if (v > tiny) return 1;
    if (v < -tiny) return -1;
    return null;
  } catch (e) {
    if (e.code === "BUDGET") throw e;
    return null;
  }
}

// ---------------- condition normalisation ----------------
const FLIP = { "<": ">", ">": "<", "<=": ">=", ">=": "<=", "!=": "!=" };
function decideFromSign(op, s) {
  if (s === null) return null;
  switch (op) {
    case ">": return s === 1 ? true : s === -1 || s === 0 || s === "np" ? false : null;
    case ">=": return s === 1 || s === 0 || s === "nn" ? true : s === -1 ? false : null;
    case "<": return s === -1 ? true : s === 1 || s === 0 || s === "nn" ? false : null;
    case "<=": return s === -1 || s === 0 || s === "np" ? true : s === 1 ? false : null;
    case "!=": return s === 1 || s === -1 || s === "nz" ? true : s === 0 ? false : null;
    default: return null;
  }
}
// d is linear in exactly one symbol with rational leading coefficient: returns [x, a, b] with d = a x + b
function linearIn(d) {
  const fs = X.freeSymbols(d);
  if (fs.size !== 1) return null;
  const name = [...fs][0];
  const x = X.sym(name);
  const terms = d.k === "add" ? d.args : [d];
  let a = null;
  const rest = [];
  for (const t of terms) {
    if (t === x) { if (a) return null; a = N.ONE; continue; }
    if (t.k === "mul" && t.args.length === 2 && t.args[0].k === "num" && t.args[1] === x) { if (a) return null; a = t.args[0].v; continue; }
    if (X.hasSym(t, name)) return null;
    rest.push(t);
  }
  if (!a) return null;
  return [x, a, rest.length ? X.add(...rest) : ZERO];
}
function decideByBounds(x, op, c, ctx) {
  const b = ctx && ctx.bounds && ctx.bounds.get(x.name);
  if (!b) return null;
  // is x op c implied (true) or contradicted (false) by lo <= x <= hi ?
  const cmpS = (u, v) => constSign(X.sub(u, v));
  if (b.lo) {
    const s = cmpS(b.lo, c); // sign(lo - c)
    if (s !== null) {
      if ((op === ">" || op === "!=") && (s === 1 || (s === 0 && b.loOpen))) return true;
      if (op === ">=" && (s === 1 || s === 0)) return true;
      if ((op === "<" && (s === 1 || (s === 0 && !b.loOpen) || (s === 0 && b.loOpen))) || (op === "<=" && (s === 1 || (s === 0 && b.loOpen)))) return false;
    }
  }
  if (b.hi) {
    const s = cmpS(b.hi, c); // sign(hi - c)
    if (s !== null) {
      if ((op === "<" || op === "!=") && (s === -1 || (s === 0 && b.hiOpen))) return true;
      if (op === "<=" && (s === -1 || s === 0)) return true;
      if ((op === ">" && (s === -1 || s === 0)) || (op === ">=" && (s === -1 || (s === 0 && b.hiOpen)))) return false;
    }
  }
  return null;
}
// Normalise ONE condition node; returns an array of condition nodes ([] means "true", [FALSE] means false).
export function normalizeCond(c, ctx, depth = 0) {
  if (depth > 40) return [c];
  if (!c) return [];
  if (c.rel && !c.k) c = c.rel; // accept { rel, reason } records
  if (c.k === "bool") return c.v ? [] : [FALSE];
  if (c.k === "and") {
    const out = [];
    for (const a of c.args) {
      const r = normalizeCond(a, ctx, depth + 1);
      if (r.includes(FALSE)) return [FALSE];
      for (const x of r) if (!out.includes(x)) out.push(x);
    }
    return out;
  }
  if (c.k === "or") {
    const kept = [];
    for (const a of c.args) {
      const r = normalizeCond(a, ctx, depth + 1);
      if (!r.length) return [];
      if (r.includes(FALSE)) continue;
      kept.push(r.length === 1 ? r[0] : X.and(...r));
    }
    if (!kept.length) return [FALSE];
    return [kept.length === 1 ? kept[0] : X.or(...kept)];
  }
  if (c.k === "not") {
    const r = normalizeCond(c.args[0], ctx, depth + 1);
    if (!r.length) return [FALSE];
    if (r.includes(FALSE)) return [];
    return [X.not(r.length === 1 ? r[0] : X.and(...r))];
  }
  if (c.k === "fn" && c.name === "isInteger") {
    const v = safeSimplify(c.args[0], ctx);
    if (!v || v === UNDEF) return [FALSE];
    if (v.k === "num") return v.v.d === 1n ? [] : [FALSE];
    if (v.k === "sym") { const t = tagsOf(ctx, v.name); if (t && t.has("integer")) return []; }
    return [X.fn("isInteger", v)];
  }
  if (c.k === "eq") c = X.rel("=", c.args[0], c.args[1]);
  if (c.k !== "rel") return [c];
  const op = c.op;
  const d0 = safeSimplify(X.sub(c.args[0], c.args[1]), ctx);
  if (!d0) return [c];
  if (d0 === UNDEF) return [FALSE];
  if (op === "=") {
    if (d0.k === "num") return N.isZero(d0.v) ? [] : [FALSE];
    return [X.rel("=", d0, ZERO)];
  }
  const d = d0;
  if (d.k === "num") return decideFromSign(op, N.sign(d.v)) ? [] : [FALSE];
  if (containsNode(d, I)) {
    // a non-real quantity cannot satisfy an order relation in the real domain
    if (op !== "!=" && (!ctx || ctx.domain !== "complex") && !X.freeSymbols(d).size) return [FALSE];
  }
  const dec = decideFromSign(op, signUnder(d, ctx));
  if (dec === true) return [];
  if (dec === false) return [FALSE];
  if (!X.freeSymbols(d).size) {
    const s = constSign(d);
    const r = decideFromSign(op, s);
    if (r !== null) return r ? [] : [FALSE];
  }
  // structural reductions
  if (op === "!=") {
    if (d.k === "mul") {
      const out = [];
      for (const f of d.args) {
        if (f.k === "num") continue;
        if (f.k === "pow" && f.args[1].k === "num" && N.isNeg(f.args[1].v)) continue; // nonzero where defined
        const r = normalizeCond(X.rel("!=", f, ZERO), ctx, depth + 1);
        if (r.includes(FALSE)) return [FALSE];
        for (const x of r) if (!out.includes(x)) out.push(x);
      }
      return out;
    }
    if (d.k === "pow" && d.args[1].k === "num" && N.isPos(d.args[1].v)) return normalizeCond(X.rel("!=", d.args[0], ZERO), ctx, depth + 1);
    if (d.k === "fn" && d.name === "abs") return normalizeCond(X.rel("!=", d.args[0], ZERO), ctx, depth + 1);
  }
  // 1/u has the sign of u (where defined): 1/y > 0 <=> y > 0
  if (op !== "!=" && d.k === "pow" && d.args[1].k === "num" && d.args[1].v.d === 1n && d.args[1].v.n < 0n && d.args[1].v.n % 2n !== 0n)
    return normalizeCond(X.rel(op === ">=" ? ">" : op === "<=" ? "<" : op, d.args[0], ZERO), ctx, depth + 1);
  if ((op === ">" || op === ">=") && d.k === "fn" && d.name === "abs") {
    return op === ">" ? normalizeCond(X.rel("!=", d.args[0], ZERO), ctx, depth + 1) : [];
  }
  if (op === ">" && d.k === "pow" && d.args[1].k === "num" && d.args[1].v.d === 1n && d.args[1].v.n % 2n === 0n && d.args[1].v.n > 0n)
    return normalizeCond(X.rel("!=", d.args[0], ZERO), ctx, depth + 1);
  if (op === ">" && d.k === "mul" && d.args.length === 2 && d.args[0].k === "fn" && d.args[0].name === "abs" && d.args[1].k === "fn" && d.args[1].name === "abs")
    return normalizeCond(X.rel("!=", d, ZERO), ctx, depth + 1);
  // linear in one symbol: x op c
  const lin = linearIn(d);
  if (lin) {
    const [x, a, b] = lin;
    const cval = safeSimplify(X.mul(X.num(N.neg(N.inv(a))), b), ctx);
    const op2 = N.isNeg(a) ? FLIP[op] : op;
    if (cval) {
      const byB = decideByBounds(x, op2, cval, ctx);
      if (byB === true) return [];
      if (byB === false) return [FALSE];
      return [X.rel(op2, x, cval)];
    }
  }
  // readable form: move the numeric constant to the right, prefer a positive leading part
  let lhs = d, rhs = ZERO, op3 = op;
  if (d.k === "add" && d.args.some((a) => a.k === "num")) {
    const cst = d.args.find((a) => a.k === "num");
    lhs = safeSimplify(X.sub(d, cst), ctx) || d;
    rhs = X.num(N.neg(cst.v));
  }
  const terms = lhs.k === "add" ? lhs.args : [lhs];
  if (terms.every((t) => N.isNeg(X.coeffAndTerm(t)[0]))) {
    lhs = safeSimplify(X.neg(lhs), ctx) || lhs;
    rhs = X.num(N.neg(rhs.v));
    op3 = FLIP[op];
  }
  return [X.rel(op3, lhs, rhs)];
}
export function normalizeConditions(list, ctx) {
  const out = [];
  for (const c of list || []) {
    const r = normalizeCond(c, ctx);
    if (r.includes(FALSE)) return null;
    for (const x of r) if (!out.includes(x)) out.push(x);
  }
  return out;
}
export function decideRel(c, ctx) {
  const r = normalizeCond(c, ctx);
  if (!r.length) return true;
  if (r.includes(FALSE)) return false;
  return null;
}

// ---------------- domain inference ----------------
function isPositiveConst(u) {
  if (u === E || u === PI) return true;
  if (u.k === "num") return N.isPos(u.v);
  if (X.freeSymbols(u).size) return false;
  return constSign(u) === 1;
}
function isIntegerExpr(u, ctx) {
  if (u.k === "num") return u.v.d === 1n;
  if (u.k === "sym") { const t = tagsOf(ctx, u.name); return !!(t && t.has("integer")); }
  if (u.k === "add" || u.k === "mul") return u.args.every((a) => isIntegerExpr(a, ctx));
  return false;
}

export function inferDomain(tree, opts = {}) {
  const ctx = opts.ctx || makeCtx({ domain: opts.domain });
  const real = ctx.domain !== "complex";
  const raw = [];
  const push = (rel, reason, sub) => raw.push({ rel, reason, sub });
  const canon = (u) => safeSimplify(u, ctx) || u;
  let steps = 0;
  const walk = (u) => {
    if (++steps > 20000) throw budgetErr("domain inference");
    switch (u.k) {
      case "const":
        if (u === UNDEF) push(FALSE, "the expression contains an undefined value", u);
        break;
      case "pow": {
        const b = u.args[0];
        let e = u.args[1];
        if (e.k !== "num") { const ce = canon(e); if (ce.k === "num") e = ce; }
        if (e.k === "num") {
          if (N.isNeg(e.v)) push(X.rel("!=", canon(b), ZERO), "a denominator cannot be zero", b);
          if (real && e.v.d % 2n === 0n) {
            if (N.isNeg(e.v)) push(X.rel(">", canon(b), ZERO), "an even root in a denominator needs a positive radicand", b);
            else push(X.rel(">=", canon(b), ZERO), "an even root needs a nonnegative radicand (real numbers)", b);
          }
        } else if (b === E || isPositiveConst(b)) {
          // a^x with a > 0 is defined for every real x
        } else if (b.k === "num" && N.isZero(b.v)) {
          push(X.rel(">", canon(e), ZERO), "0^y is defined only for y > 0", u);
        } else if (b.k === "num" && N.isNeg(b.v)) {
          push(X.fn("isInteger", canon(e)), "a negative base needs an integer exponent (real numbers)", u);
        } else if (isIntegerExpr(e, ctx)) {
          const se = signUnder(canon(e), ctx);
          if (!(se === 1 || se === "nn" || se === 0)) push(X.rel("!=", canon(b), ZERO), "a negative integer power is a division; the base cannot be zero", b);
        } else if (real) {
          push(X.rel(">", canon(b), ZERO), "a power with a symbolic (possibly non-integer) exponent is defined here for a positive base", b);
        }
        break;
      }
      case "fn": {
        const a = u.args;
        const x = a[0] ? canon(a[0]) : null;
        switch (u.name) {
          case "ln":
            push(real ? X.rel(">", x, ZERO) : X.rel("!=", x, ZERO), real ? "the logarithm needs a positive argument" : "the logarithm of 0 is undefined", a[0]);
            break;
          case "log": {
            const [bb, yy] = a.length === 1 ? [X.num(10), a[0]] : a;
            push(real ? X.rel(">", canon(yy), ZERO) : X.rel("!=", canon(yy), ZERO), "the logarithm needs a positive argument", yy);
            push(X.rel(">", canon(bb), ZERO), "a logarithm base must be positive", bb);
            push(X.rel("!=", canon(bb), ONE), "a logarithm base cannot be 1", bb);
            break;
          }
          case "sqrt":
            if (real) push(X.rel(">=", x, ZERO), "an even root needs a nonnegative radicand (real numbers)", a[0]);
            break;
          case "asin": case "acos":
            if (real) {
              push(X.rel(">=", x, NEG_ONE), `${u.name} needs an argument in [-1, 1]`, a[0]);
              push(X.rel("<=", x, ONE), `${u.name} needs an argument in [-1, 1]`, a[0]);
            }
            break;
          case "asec": case "acsc":
            if (real) push(X.rel(">=", X.fn("abs", x), ONE), `${u.name} needs |argument| >= 1`, a[0]);
            break;
          case "acosh":
            if (real) push(X.rel(">=", x, ONE), "acosh needs an argument >= 1", a[0]);
            break;
          case "atanh":
            if (real) { push(X.rel(">", x, NEG_ONE), "atanh needs an argument in (-1, 1)", a[0]); push(X.rel("<", x, ONE), "atanh needs an argument in (-1, 1)", a[0]); }
            break;
          case "tan": case "sec":
            push(X.rel("!=", canon(X.fn("cos", x)), ZERO), `${u.name} is undefined where cos = 0`, a[0]);
            break;
          case "cot": case "csc":
            push(X.rel("!=", canon(X.fn("sin", x)), ZERO), `${u.name} is undefined where sin = 0`, a[0]);
            break;
          case "factorial":
            push(X.not(X.and(X.fn("isInteger", x), X.rel("<", x, ZERO))), "the factorial is undefined at negative integers", a[0]);
            break;
          case "gamma":
            push(X.not(X.and(X.fn("isInteger", x), X.rel("<=", x, ZERO))), "the gamma function is undefined at 0 and negative integers", a[0]);
            break;
          case "mod":
            if (a[1]) push(X.rel("!=", canon(a[1]), ZERO), "mod by zero is undefined", a[1]);
            break;
          case "root":
            if (a[1]) push(X.rel("!=", canon(a[1]), ZERO), "a root index cannot be zero", a[1]);
            break;
          default: break;
        }
        break;
      }
      default: break;
    }
    // bound-variable constructs: do not leak conditions on the bound variable
    if (["sum", "product", "integral", "limit", "deriv", "quant", "fndef", "piecewise"].includes(u.k)) return;
    for (const c of u.args) walk(c);
  };
  walk(tree);
  const conditions = [];
  let empty = false;
  for (const r of raw) {
    const norm = normalizeCond(r.rel, ctx);
    if (norm.includes(FALSE)) { empty = true; conditions.push({ rel: FALSE, reason: r.reason, sub: r.sub }); continue; }
    for (const n of norm) if (!conditions.some((c) => c.rel === n)) conditions.push({ rel: n, reason: r.reason, sub: r.sub });
  }
  const tight = tightenConditions(conditions);
  return { conditions: tight, rels: tight.map((c) => c.rel), empty: empty || tight.some((c) => c.rel === FALSE) };
}

// Merge simple bounds on the same expression: "L >= a" and "L > b" keep only the tighter one,
// "L != c" together with "L >= c" becomes "L > c", "L != c" outside the bounds is dropped,
// and incompatible bounds give FALSE. Only conditions "L op q" with q an exact rational take part.
export function tightenConditions(conditions) {
  const groups = new Map();
  const isB = (r) => r && r.k === "rel" && r.args[1].k === "num" && ["<", "<=", ">", ">=", "!="].includes(r.op);
  for (const c of conditions) if (isB(c.rel)) {
    const L = c.rel.args[0];
    if (!groups.has(L)) groups.set(L, []);
    groups.get(L).push(c);
  }
  if (!groups.size) return conditions;
  const drop = new Set(), add = [];
  for (const [L, cs] of groups) {
    if (cs.length < 2) continue;
    let lo = null, hi = null;
    for (const c of cs) {
      const { op } = c.rel, q = c.rel.args[1].v;
      if (op === ">" || op === ">=") {
        const open = op === ">";
        if (!lo || N.lt(lo.q, q) || (N.eq(lo.q, q) && open && !lo.open)) lo = { q, open, c };
      } else if (op === "<" || op === "<=") {
        const open = op === "<";
        if (!hi || N.lt(q, hi.q) || (N.eq(hi.q, q) && open && !hi.open)) hi = { q, open, c };
      }
    }
    const kept = [];
    for (const c of cs) {
      const { op } = c.rel, q = c.rel.args[1].v;
      if (op === "!=") {
        if ((lo && (N.lt(q, lo.q) || (N.eq(q, lo.q) && lo.open))) || (hi && (N.lt(hi.q, q) || (N.eq(q, hi.q) && hi.open)))) { drop.add(c); continue; }
        if (lo && N.eq(q, lo.q)) { drop.add(c); lo = { ...lo, open: true, changed: true }; continue; }
        if (hi && N.eq(q, hi.q)) { drop.add(c); hi = { ...hi, open: true, changed: true }; continue; }
        kept.push(c);
      } else if (c !== (lo && lo.c) && c !== (hi && hi.c)) drop.add(c);
    }
    for (const b of [lo, hi]) if (b && b.changed) {
      drop.add(b.c);
      add.push({ at: b.c, rec: { ...b.c, rel: X.rel(b === lo ? ">" : "<", L, X.num(b.q)) } });
    }
    if (lo && hi && (N.lt(hi.q, lo.q) || (N.eq(hi.q, lo.q) && (lo.open || hi.open)))) {
      add.push({ at: lo.c, rec: { rel: FALSE, reason: "the conditions on " + toText(L) + " are incompatible", sub: L } });
    }
  }
  const out = [];
  for (const c of conditions) {
    for (const a of add) if (a.at === c) out.push(a.rec);
    if (!drop.has(c)) out.push(c);
  }
  return out;
}
export const domainConditions = (tree, opts) => inferDomain(tree, opts).rels;

// Domain of an equation plus the conditions that squaring would otherwise lose:
// sqrt(A) = B requires B >= 0 (this rejects extraneous roots such as x = -1 in sqrt(x + 2) = x).
export function equationConditions(eqNode, opts = {}) {
  const ctx = opts.ctx || makeCtx({ domain: opts.domain });
  if (eqNode.k !== "eq") return inferDomain(eqNode, opts);
  const [l, r] = eqNode.args;
  const out = [...inferDomain(l, { ctx }).conditions];
  for (const c of inferDomain(r, { ctx }).conditions) if (!out.some((o) => o.rel === c.rel)) out.push(c);
  const evenRootSide = (u) => {
    if (u.k === "pow" && u.args[1].k === "num" && u.args[1].v.d % 2n === 0n && N.isPos(u.args[1].v)) return true;
    if (u.k === "fn" && (u.name === "sqrt" || u.name === "abs")) return true;
    if (u.k === "mul" && u.args.length === 2 && u.args[0].k === "num" && N.isPos(u.args[0].v)) return evenRootSide(u.args[1]);
    return false;
  };
  for (const [a, b] of [[l, r], [r, l]]) {
    if (evenRootSide(a) && !evenRootSide(b)) {
      const norm = normalizeCond(X.rel(">=", b, ZERO), ctx);
      const reason = "an even root (or absolute value) is nonnegative, so the other side must be >= 0";
      if (norm.includes(FALSE)) out.push({ rel: FALSE, reason, sub: b });
      else for (const n of norm) if (!out.some((o) => o.rel === n)) out.push({ rel: n, reason, sub: b });
    }
  }
  const tight = tightenConditions(out);
  return { conditions: tight, rels: tight.map((c) => c.rel), empty: tight.some((c) => c.rel === FALSE) };
}

// ---------------- point checking ----------------
function toNode(v) {
  if (v && typeof v === "object" && v.k) return v;
  if (v && typeof v === "object" && "n" in v && "d" in v) return X.num(v);
  if (typeof v === "bigint") return X.num(v);
  if (typeof v === "number") {
    if (Number.isInteger(v)) return X.num(v);
    return X.num(N.fromDecimal(String(v)));
  }
  if (typeof v === "string") return safeSimplify(parse(v)) || parse(v);
  throw new TypeError("checkPoint: bad value " + v);
}
export function envToMap(env) {
  const m = new Map();
  if (!env) return m;
  const entries = env instanceof Map ? [...env] : Object.entries(env);
  for (const [k, v] of entries) m.set(k, toNode(v));
  return m;
}
// Decide one condition at a point. Returns { holds: true|false|null, method }.
function evalCond(c, env, ctx, depth = 0) {
  if (depth > 40) return { holds: null, method: "depth" };
  if (c.rel && !c.k) c = c.rel;
  switch (c.k) {
    case "bool": return { holds: c.v, method: "exact" };
    case "and": case "or": {
      let method = "exact", unknown = false;
      for (const a of c.args) {
        const r = evalCond(a, env, ctx, depth + 1);
        if (r.method !== "exact") method = r.method;
        if (r.holds === null) { unknown = true; continue; }
        if (c.k === "and" && !r.holds) return { holds: false, method: r.method };
        if (c.k === "or" && r.holds) return { holds: true, method: r.method };
      }
      return { holds: unknown ? null : c.k === "and", method };
    }
    case "not": {
      const r = evalCond(c.args[0], env, ctx, depth + 1);
      return { holds: r.holds === null ? null : !r.holds, method: r.method };
    }
    case "fn":
      if (c.name === "isInteger") {
        const v = safeSimplify(X.subs(c.args[0], env), ctx);
        if (!v || v === UNDEF) return { holds: false, method: "exact" };
        if (v.k === "num") return { holds: v.v.d === 1n, method: "exact" };
        return { holds: null, method: "exact" };
      }
      return { holds: null, method: "unsupported" };
    case "eq": case "rel": {
      const op = c.k === "eq" ? "=" : c.op;
      const d = safeSimplify(X.subs(X.sub(c.args[0], c.args[1]), env), ctx);
      if (!d || d === UNDEF || X.contains(d, UNDEF)) return { holds: false, method: "exact", note: "undefined at this point" };
      const cmp = (s) => ({ "<": s < 0, "<=": s <= 0, ">": s > 0, ">=": s >= 0, "!=": s !== 0, "=": s === 0 }[op]);
      if (d.k === "num") return { holds: cmp(N.sign(d.v)), method: "exact" };
      if (X.freeSymbols(d).size) return { holds: null, method: "symbolic" };
      if (X.contains(d, I)) {
        if (op === "!=" || op === "=") {
          const f = evalNumeric(d, {}, { mode: "complex" });
          if (f && Math.hypot(f.re, f.im) > 1e-9) return { holds: op === "!=", method: "numeric-double" };
          return { holds: null, method: "numeric-double" };
        }
        return { holds: false, method: "exact", note: "not a real number" };
      }
      const s = signUnder(d, ctx);
      if (s === 1 || s === -1 || s === 0) return { holds: cmp(s), method: "exact" };
      const hp = hpSign(d);
      if (hp !== null) return { holds: cmp(hp), method: "numeric-high-precision" };
      const f = evalNumeric(d, {}, { mode: "real" });
      if (f && Math.abs(f.re) > 1e-9) return { holds: cmp(Math.sign(f.re)), method: "numeric-double" };
      return { holds: null, method: "numeric-double" };
    }
    default: return { holds: null, method: "unsupported" };
  }
}
// conditions: array of condition nodes or { rel, reason } records (e.g. inferDomain(...).conditions),
// or the result object of inferDomain itself. env: { x: "3" | 3 | node | Rational }.
export function checkPoint(conditions, env, opts = {}) {
  const ctx = opts.ctx || makeCtx({ domain: opts.domain });
  const list = Array.isArray(conditions) ? conditions : conditions && conditions.conditions ? conditions.conditions : [];
  const m = envToMap(env);
  const results = [], violated = [], undecided = [];
  let method = "exact";
  for (const c of list) {
    const node = c.rel && !c.k ? c.rel : c;
    const r = evalCond(node, m, ctx);
    const rec = { condition: node, reason: c.reason || null, holds: r.holds, method: r.method, text: toText(node) };
    results.push(rec);
    if (r.method !== "exact" && r.method !== "symbolic") method = "numeric";
    if (r.holds === false) violated.push(rec);
    else if (r.holds === null) undecided.push(rec);
  }
  return {
    ok: violated.length ? false : undecided.length ? null : true,
    results, violated, undecided, method,
    note: method === "numeric" ? "some conditions were decided by high-precision numerical sign determination" : undefined,
  };
}

// ---------------- simplification under assumptions ----------------
export function simplifyUnder(tree, assumptions, opts = {}) {
  const ctx = makeAssumeCtx(assumptions, opts);
  const out = simplifyFull(tree, { ...opts, ctx });
  return { ...out, ctx };
}
