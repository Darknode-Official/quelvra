// Quelvra automatic simplification (the canonicaliser).
//
// Produces the canonical form every other engine relies on:
//   * numbers folded exactly, like terms collected (x + 2x -> 3x), like bases merged (x*x -> x^2)
//   * n-ary add / mul flattened and sorted by the canonical order in expr.js
//   * only transformations that are valid everywhere the input is defined are applied
//     automatically. Cancellations that need a condition (x/x -> 1 needs x != 0) are
//     applied, and the condition is REPORTED through ctx.conditions so solvers and the
//     step engine can state it (and so the domain module can reject values).
//   * power rules are domain-aware: sqrt(x^2) -> |x| over the reals, (x^a)^b merged only when valid
//
// Nothing is expanded automatically: 2(x+y) stays a product. expand() is a separate, explicit rule.

import * as N from "./num.js";
import {
  mk, num, sym, konst, add as rawAdd, mul as rawMul, pow as rawPow, fn as rawFn, withArgs,
  ZERO, ONE, TWO, NEG_ONE, HALF, PI, E, I, OO, UNDEF, TRUE, FALSE,
  isNum, isInt, isZero, isOne, before, sortArgs, coeffAndTerm, baseExp, freeSymbols, bool,
} from "./expr.js";

// ---------------- context ----------------
// domain: "real" (default, school convention: odd roots of negatives are real) or "complex"
// assume: Map<symbolName, Set<"positive"|"nonnegative"|"nonzero"|"integer"|"real"|"negative">>
// conditions: array collecting { node, rel: "!=0" | ">=0" | ">0", reason } produced by simplification
export function makeCtx(opts = {}) {
  return {
    domain: opts.domain || "real",
    assume: opts.assume || new Map(),
    conditions: opts.conditions || null,
    budget: typeof opts.budget === "number" ? { ops: opts.budget } : opts.budget || { ops: 2_000_000 },
  };
}
const DEFAULT_CTX = makeCtx();
let CTX = DEFAULT_CTX;

function note(node, rel, reason) {
  if (CTX.conditions && !isNum(node)) {
    if (!CTX.conditions.some((c) => c.node === node && c.rel === rel)) CTX.conditions.push({ node, rel, reason });
  }
}
function tick() {
  if (--CTX.budget.ops < 0) {
    const e = new Error("Quelvra: operation budget exhausted");
    e.code = "BUDGET";
    throw e;
  }
}

// ---------------- sign / domain knowledge ----------------
function hasAssume(name, a) {
  const s = CTX.assume.get(name);
  return !!s && s.has(a);
}
// Is u known to be real? (symbols are real in the real domain)
export function isReal(u) {
  switch (u.k) {
    case "num": return true;
    case "const": return u.name === "pi" || u.name === "e";
    case "sym": return CTX.domain === "real" || hasAssume(u.name, "real") || hasAssume(u.name, "positive");
    case "add": case "mul": return u.args.every(isReal);
    case "pow": {
      const [b, e] = u.args;
      if (!isReal(b) || !isReal(e)) return false;
      if (isInt(e)) return true;
      return CTX.domain === "real";
    }
    case "fn": return ["abs", "sin", "cos", "tan", "exp", "atan", "sinh", "cosh", "tanh", "floor", "ceil", "sign"].includes(u.name) && u.args.every(isReal)
      || (CTX.domain === "real" && u.args.every(isReal));
    default: return false;
  }
}
// Known sign: 1 (>0), 0 (=0), -1 (<0), "nn" (>=0), "np" (<=0), null unknown
export function signOf(u) {
  switch (u.k) {
    case "num": return N.sign(u.v);
    case "const": return u.name === "pi" || u.name === "e" || u.name === "oo" ? 1 : null;
    case "sym":
      if (hasAssume(u.name, "positive")) return 1;
      if (hasAssume(u.name, "negative")) return -1;
      if (hasAssume(u.name, "nonnegative")) return "nn";
      return null;
    case "pow": {
      const [b, e] = u.args;
      const sb = signOf(b);
      if (sb === 1) return 1;
      if (isInt(e) && e.v.n % 2n === 0n && isReal(b)) return sb === 0 ? 0 : "nn";
      if (isNum(e) && e.v.d % 2n === 0n && CTX.domain === "real") return "nn"; // even root
      if (b === E && isReal(e)) return 1;
      return null;
    }
    case "mul": {
      let s = 1, weak = false;
      for (const a of u.args) {
        const t = signOf(a);
        if (t === null) return null;
        if (t === 0) return 0;
        if (t === "nn") weak = true;
        else if (t === "np") { weak = true; s = -s; }
        else s *= t;
      }
      return weak ? (s > 0 ? "nn" : "np") : s;
    }
    case "add": {
      let pos = 0, neg = 0, nn = 0, np = 0;
      for (const a of u.args) {
        const t = signOf(a);
        if (t === null) return null;
        if (t === 1) pos++; else if (t === -1) neg++; else if (t === "nn") nn++; else if (t === "np") np++;
      }
      if (!neg && !np && pos) return 1;
      if (!pos && !nn && neg) return -1;
      if (!neg && !np) return "nn";
      if (!pos && !nn) return "np";
      return null;
    }
    case "fn":
      if (u.name === "abs") return signOf(u.args[0]) === 0 ? 0 : "nn";
      if (u.name === "exp") return 1;
      if (u.name === "sqrt") return "nn";
      return null;
    default: return null;
  }
}
const isPositive = (u) => signOf(u) === 1;
const isNonNeg = (u) => { const s = signOf(u); return s === 1 || s === 0 || s === "nn"; };
const isNonZero = (u) => { const s = signOf(u); return s === 1 || s === -1; };

// ---------------- public entry ----------------
const MEMO = { real: new Map(), complex: new Map() };

// The default context's budget is refilled at every top-level entry (a call made while no other
// simplification is running), so long-lived callers such as a Web Worker never exhaust it; an
// explicit ctx keeps its own budget for the lifetime of that ctx.
let DEPTH = 0;
const DEFAULT_OPS = 2_000_000;
function topLevel(fn) {
  if (DEPTH === 0 && CTX === DEFAULT_CTX) DEFAULT_CTX.budget.ops = DEFAULT_OPS;
  DEPTH++;
  try { return fn(); } finally { DEPTH--; }
}
export function simplify(u, ctx) {
  const prev = CTX;
  if (DEPTH === 0 && !ctx) DEFAULT_CTX.budget.ops = DEFAULT_OPS;
  CTX = ctx || DEFAULT_CTX;
  DEPTH++;
  try {
    return simp(u);
  } finally {
    DEPTH--;
    CTX = prev;
  }
}

function simp(u) {
  // Memoise only when no assumptions/conditions are active (pure mode).
  const pure = CTX.assume.size === 0 && !CTX.conditions;
  const memo = MEMO[CTX.domain] || MEMO.real;
  if (pure) {
    const hit = memo.get(u);
    if (hit) return hit;
  }
  tick();
  let r;
  if (!u.args.length) r = u;
  else {
    const args = u.args.map(simp);
    const v = withArgs(u, args);
    r = simpNode(v);
  }
  if (pure) {
    if (memo.size > 200_000) memo.clear();
    memo.set(u, r);
  }
  return r;
}

function simpNode(u) {
  if (u.args.some((a) => a === UNDEF) && !["piecewise", "set", "tuple"].includes(u.k)) return UNDEF;
  switch (u.k) {
    case "pow": return simpPow(u.args[0], u.args[1]);
    case "mul": return simpMul(u.args);
    case "add": return simpAdd(u.args);
    case "fn": return simpFn(u.name, u.args);
    case "eq": return simpEq(u);
    case "rel": return simpRel(u);
    case "and": case "or": return simpLogic(u);
    case "not": return u.args[0].k === "bool" ? bool(!u.args[0].v) : u;
    case "set": return simpSet(u);
    default: return u;
  }
}

// ---------------- numbers ----------------
const Nn = (r) => num(r);

// r^(p/q) for rational r, exact where possible. Returns a node.
function ratPow(r, e) {
  if (e.d === 1n) {
    if (N.isZero(r) && e.n < 0n) return UNDEF;
    return Nn(N.pow(r, e.n));
  }
  if (N.isZero(r)) return e.n > 0n ? ZERO : UNDEF;
  if (N.isOne(r)) return ONE;
  // negative base
  if (N.isNeg(r)) {
    if (e.d % 2n === 1n && CTX.domain === "real") {
      // real odd root: (-a)^(p/q) = (-1)^p * a^(p/q)
      const pos = ratPow(N.neg(r), e);
      return e.n % 2n === 0n ? pos : simpMul([NEG_ONE, pos]);
    }
    if (e.d === 2n) {
      // principal branch: (-a)^(p/2) = (I)^p * a^(p/2)
      return simpMul([simpPow(I, num(e.n)), ratPow(N.neg(r), e)]);
    }
    if (CTX.domain === "real") return UNDEF; // (-8)^(1/4) has no real value
    return rawPow(Nn(r), Nn(e)); // leave complex principal value symbolic
  }
  // split exponent p/q = k + s/q with 0 < s < q
  const k = N.floor(e);
  const s = e.n - k * e.d; // numerator of the fractional part over e.d
  const q = e.d;
  const whole = N.pow(r, k);
  // r^(s/q) = (num^s)^(1/q) / (den^s)^(1/q)
  const top = rootInt(r.n ** s, q);
  const bot = rootInt(r.d ** s, q);
  // rationalise: 1/root(bot) -> root(bot^(q-1)) / bot_value
  let factors = [Nn(whole), Nn(N.Q(top.outside, bot.outside))];
  if (top.inside !== 1n) factors.push(rawPow(num(top.inside), num(N.Q(1n, q))));
  if (bot.inside !== 1n) {
    // multiply by bot.inside^((q-1)/q) / bot.inside
    const r2 = rootInt(bot.inside ** (q - 1n), q);
    factors.push(Nn(N.Q(r2.outside, bot.inside)));
    if (r2.inside !== 1n) factors.push(rawPow(num(r2.inside), num(N.Q(1n, q))));
  }
  return mergeRadicals(factors, q);
}
function rootInt(n, q) {
  if (n === 1n) return { outside: 1n, inside: 1n };
  return N.extractPower(n, q);
}
// Multiply numeric factors and radicals with the same index into one radical.
function mergeRadicals(factors, q) {
  let c = N.ONE, rad = 1n;
  for (const f of factors) {
    if (f.k === "num") c = N.mul(c, f.v);
    else rad *= f.args[0].v.n;
  }
  if (rad !== 1n) {
    const ex = rootInt(rad, q);
    c = N.mul(c, N.Q(ex.outside));
    rad = ex.inside;
  }
  if (rad === 1n) return Nn(c);
  const radical = mk("pow", [num(rad), num(N.Q(1n, q))]);
  return N.isOne(c) ? radical : mk("mul", [Nn(c), radical]);
}

// ---------------- powers ----------------
export function simpPow(b, e) {
  tick();
  if (b === UNDEF || e === UNDEF) return UNDEF;
  if (isZero(e)) {
    if (isZero(b)) return UNDEF; // 0^0 is indeterminate
    if (!isNum(b)) note(b, "!=0", "x^0 = 1 requires x != 0");
    return ONE;
  }
  if (isOne(e)) return b;
  if (isOne(b)) return ONE;
  if (isZero(b)) {
    if (isNum(e)) return N.isPos(e.v) ? ZERO : UNDEF;
    if (isPositive(e)) return ZERO;
    return rawPow(b, e);
  }
  // infinity
  if (b === OO) {
    if (isNum(e)) return N.isPos(e.v) ? OO : ZERO;
  }
  if (isNum(b) && isNum(e)) return ratPow(b.v, e.v);
  // I^n
  if (b === I && isInt(e)) {
    const m = ((e.v.n % 4n) + 4n) % 4n;
    return [ONE, I, NEG_ONE, simpMul([NEG_ONE, I])][Number(m)];
  }
  // Euler: e^(r*I*pi) = cos(r pi) + I sin(r pi) for rational r
  if (b === E && e.k === "mul" && e.args.includes(I) && e.args.includes(PI) && e.args.every((f) => f === I || f === PI || isNum(f))) {
    const r = simpMul(e.args.filter((f) => f !== I));
    return simpAdd([simpFn("cos", [r]), simpMul([I, simpFn("sin", [r])])]);
  }
  if (b === E && e === I) return rawPow(b, e);
  // e^(ln u) = u  (valid wherever ln u is defined)
  if (b === E && e.k === "fn" && e.name === "ln") { note(e.args[0], ">0", "ln requires a positive argument"); return e.args[0]; }
  // e^(k ln u) = u^k  for rational k (u > 0 required by ln)
  if (b === E && e.k === "mul" && e.args.length === 2 && isNum(e.args[0]) && e.args[1].k === "fn" && e.args[1].name === "ln")
  { note(e.args[1].args[0], ">0", "ln requires a positive argument"); return simpPow(e.args[1].args[0], e.args[0]); }
  // (x^a)^b
  if (b.k === "pow") return powOfPow(b.args[0], b.args[1], e);
  // (u*v)^n
  if (b.k === "mul") {
    if (isInt(e)) return simpMul(b.args.map((f) => simpPow(f, e)));
    // pull out factors that are known positive (including positive numbers): (4x)^(1/2) = 2 x^(1/2)
    const pos = [], rest = [];
    for (const f of b.args) {
      if (isPositive(f)) pos.push(f);
      else if (isNum(f) && N.isNeg(f.v)) { if (!N.isOne(N.neg(f.v))) pos.push(Nn(N.neg(f.v))); rest.push(NEG_ONE); }
      else rest.push(f);
    }
    // In the real domain an odd root distributes over any product: cbrt(ab) = cbrt(a) cbrt(b)
    if (isNum(e) && e.v.d % 2n === 1n && CTX.domain === "real") return simpMul(b.args.map((f) => simpPow(f, e)));
    if (pos.length) {
      const inner = rest.length === 0 ? ONE : rest.length === 1 ? rest[0] : simpMul(rest);
      const restPow = isOne(inner) ? ONE : inner === NEG_ONE ? simpPow(NEG_ONE, e) : rawPow(inner, e);
      return simpMul([...pos.map((f) => simpPow(f, e)), restPow]);
    }
  }
  // |u|^(even integer) = u^(even) for real u
  if (b.k === "fn" && b.name === "abs" && isInt(e) && e.v.n % 2n === 0n && isReal(b.args[0])) return simpPow(b.args[0], e);
  return rawPow(b, e);
}

function powOfPow(x, a, b) {
  // integer outer exponent: always valid
  if (isInt(b)) return simpPow(x, simpMul([a, b]));
  if (isPositive(x) || (isNonNeg(x) && isNum(b) && N.isPos(b.v))) return simpPow(x, simpMul([a, b]));
  if (isNum(a) && isNum(b)) {
    const A = a.v, B = b.v;
    const aNumEven = A.n % 2n === 0n;
    if (CTX.domain === "real") {
      // (x^a)^b with even numerator of a and even denominator of b -> |x|^(ab)
      if (aNumEven && B.d % 2n === 0n && isReal(x)) return simpPow(simpFn("abs", [x]), Nn(N.mul(A, B)));
      // otherwise sign behaviour of x^a matches x (or x^a >= 0 forces x >= 0): merge
      return simpPow(x, Nn(N.mul(A, B)));
    }
    // complex domain: merge only when the result is branch-safe (|a| <= 1 and b real with a in (-1,1])
    if (N.cmp(N.abs(A), N.ONE) <= 0 && !aNumEven) return simpPow(x, Nn(N.mul(A, B)));
  }
  return rawPow(rawPow(x, a), b);
}

// ---------------- products ----------------
export function simpMul(args) {
  tick();
  // flatten
  let flat = [];
  for (const a of args) {
    if (a === UNDEF) return UNDEF;
    if (a.k === "mul") flat.push(...a.args); else flat.push(a);
  }
  if (flat.some(isZero)) {
    // 0 * u = 0, but 0 * oo is indeterminate
    if (flat.some((f) => f === OO)) return UNDEF;
    return ZERO;
  }
  // numeric coefficient
  let c = N.ONE;
  const rest = [];
  for (const f of flat) {
    if (isNum(f)) c = N.mul(c, f.v);
    else rest.push(f);
  }
  if (N.isZero(c)) return ZERO;
  // group by base, sum exponents
  const groups = new Map(); // base -> list of exponents
  const order = [];
  for (const f of rest) {
    const [b, e] = baseExp(f);
    if (!groups.has(b)) { groups.set(b, []); order.push(b); }
    groups.get(b).push(e);
  }
  const out = [];
  for (const b of order) {
    const exps = groups.get(b);
    if (exps.length === 1) { out.push(exps[0] === ONE ? b : simpPow(b, exps[0])); continue; }
    // combining x^a * x^b = x^(a+b): safe for integer exponents; for radicals of the same base
    // it is valid wherever both factors are defined (x >= 0 for even roots)
    const hadNeg = exps.some((e) => isNum(e) && N.isNeg(e.v)) || exps.some((e) => !isNum(e));
    const total = simpAdd(exps);
    // the base leaves the denominator (x^2/x = x, x/x = 1): the original needed b != 0
    if (hadNeg && !isNum(b) && !(isNum(total) && N.isNeg(total.v))) note(b, "!=0", "cancelling a factor requires it to be nonzero");
    const p = simpPow(b, total);
    out.push(p);
  }
  // re-flatten (powers may have produced numbers / products)
  const fin = [];
  for (const f of out) {
    if (isNum(f)) c = N.mul(c, f.v);
    else if (f.k === "mul") {
      for (const g of f.args) if (isNum(g)) c = N.mul(c, g.v); else fin.push(g);
    } else fin.push(f);
  }
  if (N.isZero(c)) return ZERO;
  // If re-flattening produced new like bases (e.g. sqrt2*sqrt2 from separate radicals), merge again.
  const bases = new Set();
  let dup = false;
  for (const f of fin) { const b = baseExp(f)[0]; if (bases.has(b)) dup = true; bases.add(b); }
  if (dup) return simpMul([Nn(c), ...fin]);
  // numeric radicals with the same root index combine: 2^(1/2) * 3^(1/2) = 6^(1/2)
  const merged = mergeNumericRadicals(fin);
  if (merged) return simpMul([Nn(c), ...merged]);
  const sorted = sortArgs(fin);
  if (!sorted.length) return Nn(c);
  if (N.isOne(c)) return sorted.length === 1 ? sorted[0] : mk("mul", sorted);
  return mk("mul", [Nn(c), ...sorted]);
}
function mergeNumericRadicals(fs) {
  const byIdx = new Map();
  for (const f of fs) {
    if (f.k === "pow" && isInt(f.args[0]) && isNum(f.args[1]) && f.args[1].v.n === 1n && f.args[1].v.d > 1n && f.args[0].v.n > 0n) {
      const q = f.args[1].v.d;
      if (!byIdx.has(q)) byIdx.set(q, []);
      byIdx.get(q).push(f);
    }
  }
  for (const [q, list] of byIdx) {
    if (list.length > 1) {
      let prod = 1n;
      for (const f of list) prod *= f.args[0].v.n;
      const others = fs.filter((f) => !list.includes(f));
      return [...others, ratPow(N.Q(prod), N.Q(1n, q))];
    }
  }
  return null;
}

// ---------------- sums ----------------
const addTerms = (u) => (u.k === "add" ? u.args.length : u === ZERO ? 0 : 1);
const scaledSum = (f) => f.k === "mul" && coeffAndTerm(f)[1].k === "add";
export function simpAdd(args) {
  tick();
  let flat = [];
  for (const a of args) {
    if (a === UNDEF) return UNDEF;
    if (a.k === "add") flat.push(...a.args); else flat.push(a);
  }
  const plain = simpAddFlat(flat);
  // k*(a + b) next to other terms: distribute only when terms then cancel (x + 1 - (x + 1) -> 0),
  // so intended forms such as 6(x - 3) + 9 are kept
  if (flat.length > 1 && plain.k === "add" && flat.some(scaledSum)) {
    const dist = [];
    for (const f of flat) {
      if (!scaledSum(f)) { dist.push(f); continue; }
      const [k, t] = coeffAndTerm(f);
      for (const a of t.args) dist.push(simpMul([Nn(k), a]));
    }
    const d = simpAddFlat(dist.flatMap((a) => (a.k === "add" ? a.args : [a])));
    if (d !== UNDEF && addTerms(d) < addTerms(plain)) return d;
  }
  return plain;
}
function simpAddFlat(flat) {
  // infinities
  const infs = flat.filter((f) => f === OO || (f.k === "mul" && f.args.includes(OO)));
  if (infs.length) {
    const signs = new Set(infs.map((f) => (f === OO ? 1 : N.sign(coeffAndTerm(f)[0]))));
    if (signs.size > 1) return UNDEF; // oo - oo
    return infs[0];
  }
  let c = N.ZERO;
  const coeffs = new Map(); // term -> Rational
  const order = [];
  for (const f of flat) {
    if (isNum(f)) { c = N.add(c, f.v); continue; }
    const [k, t] = coeffAndTerm(f);
    if (!coeffs.has(t)) { coeffs.set(t, N.ZERO); order.push(t); }
    coeffs.set(t, N.add(coeffs.get(t), k));
  }
  const out = [];
  for (const t of order) {
    const k = coeffs.get(t);
    if (N.isZero(k)) continue;
    out.push(N.isOne(k) ? t : simpMul([Nn(k), t]));
  }
  // numeric multiples of the same radical may now be combined differently; collect again if needed
  if (!N.isZero(c)) out.push(Nn(c));
  if (!out.length) return ZERO;
  if (out.length === 1) return out[0];
  // after simpMul some terms could be numbers or sums again
  if (out.some((f) => f.k === "add")) return simpAdd(out);
  return mk("add", sortArgs(out));
}

// ---------------- functions ----------------
const TRIG_TABLE = (() => {
  // exact values at k*pi/12 for sin; built lazily from formulas
  return null;
})();

// Returns multiple of pi as Rational if u = r*pi, else null
function piMultiple(u) {
  if (u === PI) return N.ONE;
  if (isZero(u)) return N.ZERO;
  if (u.k === "mul" && u.args.length === 2 && isNum(u.args[0]) && u.args[1] === PI) return u.args[0].v;
  return null;
}
const sqrtOf = (n) => simpPow(num(n), HALF);
function sinExact(r) {
  // r = multiple of pi; reduce to [0, 2)
  let t = N.sub(r, N.mul(N.Q(2), N.Q(N.floor(N.div(r, N.Q(2))))));
  let s = 1;
  if (N.cmp(t, N.ONE) >= 0) { t = N.sub(t, N.ONE); s = -1; } // sin(x+pi) = -sin x
  if (N.cmp(t, N.HALF) > 0) t = N.sub(N.ONE, t); // sin(pi - x) = sin x
  const key = N.toString(t);
  const table = {
    "0": ZERO,
    "1/12": null, "1/6": HALF, "1/4": null, "1/3": null, "1/2": ONE,
  };
  let v;
  switch (key) {
    case "0": v = ZERO; break;
    case "1/6": v = HALF; break;
    case "1/4": v = simpMul([HALF, sqrtOf(2)]); break;
    case "1/3": v = simpMul([HALF, sqrtOf(3)]); break;
    case "1/2": v = ONE; break;
    case "1/12": v = simpMul([num(1, 4), simpAdd([sqrtOf(6), simpMul([NEG_ONE, sqrtOf(2)])])]); break;
    case "5/12": v = simpMul([num(1, 4), simpAdd([sqrtOf(6), sqrtOf(2)])]); break;
    case "1/10": v = simpMul([num(1, 4), simpAdd([sqrtOf(5), NEG_ONE])]); break;
    case "3/10": v = simpMul([num(1, 4), simpAdd([sqrtOf(5), ONE])]); break;
    default: return null;
  }
  void table;
  return s < 0 ? simpMul([NEG_ONE, v]) : v;
}
const negCoeff = (u) => {
  const [k] = coeffAndTerm(u);
  if (u.k === "add") return N.isNeg(coeffAndTerm(u.args[0])[0]) && u.args.every((t) => N.isNeg(coeffAndTerm(t)[0]) || isNum(t) && N.isNeg(t.v));
  return N.isNeg(k);
};
// distribute over sums so negate(-x - 2) is x + 2, not -(-x - 2) (which kept negCoeff true forever)
const negate = (u) => (u.k === "add" ? simpAdd(u.args.map((t) => simpMul([NEG_ONE, t]))) : simpMul([NEG_ONE, u]));

const INVERSE = { sin: "asin", cos: "acos", tan: "atan", sinh: "asinh", cosh: "acosh", tanh: "atanh" };

export function simpFn(name, args) {
  tick();
  const x = args[0];
  const F = (n, ...a) => rawFn(n, ...a);
  switch (name) {
    case "sqrt": return simpPow(x, HALF);
    case "cbrt": return simpPow(x, num(1, 3));
    case "root": return simpPow(args[0], simpPow(args[1], NEG_ONE)); // root(x, n)
    case "exp": return simpPow(E, x);
    case "ln": {
      if (isOne(x)) return ZERO;
      if (x === E) return ONE;
      if (isZero(x)) return UNDEF;
      if (x.k === "pow" && x.args[0] === E && isReal(x.args[1])) return x.args[1]; // ln(e^u) = u for real u
      if (isNum(x) && N.isNeg(x.v) && CTX.domain === "real") return UNDEF;
      if (isNum(x) && N.isNeg(x.v)) return simpAdd([simpFn("ln", [num(N.neg(x.v))]), simpMul([I, PI])]);
      // ln of an exact integer power: ln(8) stays ln(8) (expansion to 3 ln 2 is an explicit rule)
      return F("ln", x);
    }
    case "log": {
      // log(x) base 10, log(b, x) base b
      if (args.length === 1) return simpFn("log", [num(10), x]);
      const [b, y] = args;
      if (isOne(y)) return ZERO;
      if (b === y) return ONE;
      if (isNum(b) && isNum(y) && N.isPos(b.v) && N.isPos(y.v)) {
        const k = exactLog(b.v, y.v);
        if (k) return Nn(k);
      }
      if (y.k === "pow" && y.args[0] === b && isReal(y.args[1])) return y.args[1];
      if (b === E) return simpFn("ln", [y]);
      return F("log", b, y);
    }
    case "abs": {
      if (isNum(x)) return Nn(N.abs(x.v));
      if (x === PI || x === E || x === OO) return x;
      if (x === I) return ONE;
      const s = signOf(x);
      if (s === 1 || s === "nn" || s === 0) return x;
      if (s === -1 || s === "np") return negate(x);
      if (x.k === "fn" && x.name === "abs") return x;
      if (x.k === "mul") {
        // |c u| = |c| |u|
        const [k, t] = coeffAndTerm(x);
        if (!N.isOne(k)) return simpMul([Nn(N.abs(k)), simpFn("abs", [t])]);
        // |u v| = |u||v|
        return simpMul(x.args.map((f) => simpFn("abs", [f])));
      }
      if (x.k === "pow" && isInt(x.args[1]) && isReal(x.args[0])) return simpPow(simpFn("abs", [x.args[0]]), x.args[1]);
      if (negCoeff(x)) return F("abs", negate(x));
      return F("abs", x);
    }
    case "sign": {
      const s = signOf(x);
      if (s === 1 || s === -1 || s === 0) return num(s);
      return F("sign", x);
    }
    case "sin": case "cos": case "tan": case "cot": case "sec": case "csc": {
      const r = piMultiple(x);
      if (r) {
        const sinv = sinExact(r), cosv = sinExact(N.add(r, N.HALF));
        if (sinv && cosv) {
          const val = {
            sin: sinv, cos: cosv,
            tan: isZero(cosv) ? UNDEF : simpMul([sinv, simpPow(cosv, NEG_ONE)]),
            cot: isZero(sinv) ? UNDEF : simpMul([cosv, simpPow(sinv, NEG_ONE)]),
            sec: isZero(cosv) ? UNDEF : simpPow(cosv, NEG_ONE),
            csc: isZero(sinv) ? UNDEF : simpPow(sinv, NEG_ONE),
          }[name];
          return val;
        }
      }
      if (isZero(x)) return { sin: ZERO, cos: ONE, tan: ZERO, cot: UNDEF, sec: ONE, csc: UNDEF }[name];
      // parity: sin(-u) = -sin(u), cos(-u) = cos(u)
      if (negCoeff(x)) {
        const inner = negate(x);
        return name === "cos" || name === "sec" ? simpFn(name, [inner]) : negate(simpFn(name, [inner]));
      }
      // sin(asin u) = u
      if (x.k === "fn" && x.name === INVERSE[name]) return x.args[0];
      return F(name, x);
    }
    case "asin": case "acos": case "atan": {
      const table = {
        asin: [["0", ZERO], ["1/2", simpMul([num(1, 6), PI])], ["1", simpMul([HALF, PI])], ["-1/2", simpMul([num(-1, 6), PI])], ["-1", simpMul([num(-1, 2), PI])]],
        acos: [["1", ZERO], ["1/2", simpMul([num(1, 3), PI])], ["0", simpMul([HALF, PI])], ["-1/2", simpMul([num(2, 3), PI])], ["-1", PI]],
        atan: [["0", ZERO], ["1", simpMul([num(1, 4), PI])], ["-1", simpMul([num(-1, 4), PI])]],
      }[name];
      if (isNum(x)) {
        const k = N.toString(x.v);
        const hit = table.find(([s]) => s === k);
        if (hit) return hit[1];
        if (name !== "atan" && N.cmp(N.abs(x.v), N.ONE) > 0 && CTX.domain === "real") return UNDEF;
      }
      // exact radicals: asin(sqrt2/2) = pi/4 etc.
      const s2 = simpMul([HALF, sqrtOf(2)]), s3 = simpMul([HALF, sqrtOf(3)]), r3 = sqrtOf(3), ir3 = simpMul([num(1, 3), sqrtOf(3)]);
      const rad = {
        asin: [[s2, [1, 4]], [s3, [1, 3]]],
        acos: [[s2, [1, 4]], [s3, [1, 6]]],
        atan: [[r3, [1, 3]], [ir3, [1, 6]]],
      }[name];
      for (const [val, [p, q]] of rad) {
        if (x === val) return simpMul([num(p, q), PI]);
        if (x === negate(val)) return name === "acos" ? simpMul([num(q - p, q), PI]) : simpMul([num(-p, q), PI]);
      }
      if (name !== "acos" && negCoeff(x)) return negate(simpFn(name, [negate(x)]));
      return F(name, x);
    }
    case "sinh": case "tanh": case "asinh": case "atanh":
      if (isZero(x)) return ZERO;
      if (negCoeff(x)) return negate(simpFn(name, [negate(x)]));
      return F(name, x);
    case "cosh":
      if (isZero(x)) return ONE;
      if (negCoeff(x)) return simpFn(name, [negate(x)]);
      return F(name, x);
    case "factorial": {
      if (isInt(x)) {
        if (x.v.n < 0n) return UNDEF;
        if (x.v.n <= 5000n) return num(N.factorial(x.v.n));
      }
      if (isNum(x) && x.v.d === 2n) {
        // (n/2)! via gamma(n/2 + 1) = exact multiple of sqrt(pi)
        return simpFn("gamma", [simpAdd([x, ONE])]);
      }
      return F("factorial", x);
    }
    case "gamma": {
      if (isInt(x)) return x.v.n <= 0n ? UNDEF : simpFn("factorial", [num(x.v.n - 1n)]);
      if (isNum(x) && x.v.d === 2n) {
        // gamma(1/2) = sqrt(pi); gamma(n + 1/2) = (2n)! / (4^n n!) sqrt(pi)
        const n = (x.v.n - 1n) / 2n;
        if (n >= 0n && n < 2000n) {
          const c = N.Q(N.factorial(2n * n), 4n ** n * N.factorial(n));
          return simpMul([Nn(c), simpPow(PI, HALF)]);
        }
      }
      return F("gamma", x);
    }
    case "floor": case "ceil": {
      if (isNum(x)) return num(name === "floor" ? N.floor(x.v) : N.ceil(x.v));
      return F(name, x);
    }
    case "mod": {
      const [a, m] = args;
      if (isInt(a) && isInt(m) && m.v.n !== 0n) {
        let r = a.v.n % m.v.n;
        if (r !== 0n && (r < 0n) !== (m.v.n < 0n)) r += m.v.n;
        return num(r);
      }
      return F("mod", a, m);
    }
    case "gcd": case "lcm": {
      if (args.every(isInt)) {
        let g = args[0].v.n;
        for (const a of args.slice(1)) {
          const b = a.v.n;
          g = name === "gcd" ? N.bgcd(g, b) : (g === 0n || b === 0n ? 0n : N.babs(g * b) / N.bgcd(g, b));
        }
        return num(N.babs(g));
      }
      return F(name, ...args);
    }
    case "binomial": case "nCr": {
      const [n, k] = args;
      if (isInt(n) && isInt(k) && n.v.n >= 0n) return num(N.binom(n.v.n, k.v.n));
      return F("binomial", n, k);
    }
    case "nPr": {
      const [n, k] = args;
      if (isInt(n) && isInt(k) && n.v.n >= 0n && k.v.n >= 0n && k.v.n <= n.v.n) return num(N.factorial(n.v.n) / N.factorial(n.v.n - k.v.n));
      return F("nPr", n, k);
    }
    case "re": case "im": case "conj": {
      if (isReal(x)) return name === "im" ? ZERO : x;
      return F(name, x);
    }
    default:
      return F(name, ...args);
  }
}

// exact log_b(y) for rationals when y = b^k with k rational (b^(p/q) = y)
function exactLog(b, y) {
  if (N.isOne(b)) return null;
  // try integer and simple rational exponents: y^q = b^p
  for (let q = 1n; q <= 6n; q++) {
    const yq = N.pow(y, q);
    // find p with b^p = yq
    const lb = Math.log(N.toFloat(b)), ly = Math.log(N.toFloat(yq));
    if (!isFinite(lb) || !isFinite(ly) || lb === 0) return null;
    const p = BigInt(Math.round(ly / lb));
    if (N.eq(N.pow(b, p), yq)) return N.Q(p, q);
  }
  return null;
}

// ---------------- relations ----------------
function simpEq(u) {
  const [l, r] = u.args;
  if (l === r) return u; // identity; keep equation form (verification decides truth)
  return u;
}
function simpRel(u) {
  const [l, r] = u.args;
  if (isNum(l) && isNum(r)) {
    const c = N.cmp(l.v, r.v);
    const v = { "<": c < 0, "<=": c <= 0, ">": c > 0, ">=": c >= 0, "!=": c !== 0 }[u.op];
    return v ? TRUE : FALSE;
  }
  return u;
}
function simpLogic(u) {
  const isAnd = u.k === "and";
  const out = [];
  for (const a of u.args) {
    if (a.k === "bool") {
      if (a.v === !isAnd) return a; // short-circuit
      continue;
    }
    if (a.k === u.k) out.push(...a.args); else if (!out.includes(a)) out.push(a);
  }
  if (!out.length) return isAnd ? TRUE : FALSE;
  if (out.length === 1) return out[0];
  return mk(u.k, out);
}
function simpSet(u) {
  const seen = [];
  for (const a of u.args) if (!seen.includes(a)) seen.push(a);
  return mk("set", sortArgs(seen));
}

// ---------------- convenience builders (simplifying) ----------------
export const S = {
  add: (...a) => topLevel(() => simpAdd(a)),
  sub: (a, b) => topLevel(() => simpAdd([a, simpMul([NEG_ONE, b])])),
  mul: (...a) => topLevel(() => simpMul(a)),
  div: (a, b) => topLevel(() => simpMul([a, simpPow(b, NEG_ONE)])),
  pow: (a, b) => topLevel(() => simpPow(a, b)),
  neg: (a) => topLevel(() => simpMul([NEG_ONE, a])),
  sqrt: (a) => topLevel(() => simpPow(a, HALF)),
  fn: (name, ...a) => topLevel(() => simpFn(name, a)),
  num: (n, d) => num(n, d),
};

// ---------------- expansion (explicit, not automatic) ----------------
// expand(): distribute products over sums and expand integer powers of sums.
export function expand(u, ctx) {
  const prev = CTX;
  CTX = ctx || DEFAULT_CTX;
  try { return simp(expandRec(simp(u))); } finally { CTX = prev; }
}
function expandRec(u) {
  tick();
  if (!u.args.length) return u;
  if (u.k === "add") return simpAdd(u.args.map(expandRec));
  if (u.k === "mul") {
    let acc = ONE;
    for (const f of u.args) acc = expandProduct(acc, expandRec(f));
    return acc;
  }
  if (u.k === "pow") {
    const b = expandRec(u.args[0]), e = u.args[1];
    if (isInt(e) && e.v.n > 1n && b.k === "add") {
      if (e.v.n > 60n) throw Object.assign(new Error("Quelvra: expansion too large"), { code: "BUDGET" });
      return expandPowSum(b, e.v.n);
    }
    return simpPow(b, expandRec(e));
  }
  if (u.k === "eq" || u.k === "rel" || u.k === "fn" || u.k === "tuple" || u.k === "system") return withArgs(u, u.args.map(expandRec));
  return u;
}
function expandProduct(a, b) {
  if (a.k === "add") return simpAdd(a.args.map((t) => expandProduct(t, b)));
  if (b.k === "add") return simpAdd(b.args.map((t) => expandProduct(a, t)));
  return simpMul([a, b]);
}
function expandPowSum(b, n) {
  // binomial expansion for two terms, repeated multiplication otherwise
  if (b.args.length === 2) {
    const [f, rest] = [b.args[0], b.args[1]];
    const terms = [];
    for (let k = 0n; k <= n; k++) {
      terms.push(expandProduct(simpMul([num(N.binom(n, k)), simpPow(f, num(n - k))]), expandRec(simpPow(rest, num(k)))));
    }
    return simpAdd(terms);
  }
  let acc = ONE;
  for (let i = 0n; i < n; i++) acc = expandProduct(acc, b);
  return acc;
}

// Numerator / denominator split of a canonical expression.
export function numerDenom(u) {
  if (u.k === "pow" && isNum(u.args[1]) && N.isNeg(u.args[1].v)) return [ONE, simpPow(u.args[0], num(N.neg(u.args[1].v)))];
  if (u.k === "num") return [num(u.v.n), num(u.v.d)];
  if (u.k === "mul") {
    const n = [], d = [];
    for (const f of u.args) {
      const [a, b] = numerDenom(f);
      if (!isOne(a)) n.push(a);
      if (!isOne(b)) d.push(b);
    }
    return [simpMul(n), simpMul(d)];
  }
  return [u, ONE];
}

// Put a sum over a common denominator: a/b + c/d -> (ad + bc)/(bd)
export function together(u, ctx) {
  const prev = CTX;
  CTX = ctx || DEFAULT_CTX;
  try {
    u = simp(u);
    if (u.k !== "add") return u;
    const parts = u.args.map(numerDenom);
    const dens = [];
    for (const [, d] of parts) for (const f of d.k === "mul" ? d.args : [d]) {
      const [b, e] = baseExp(f);
      const idx = dens.findIndex(([bb]) => bb === b);
      if (idx < 0) dens.push([b, e]);
      else if (isNum(e) && isNum(dens[idx][1]) && N.lt(dens[idx][1].v, e.v)) dens[idx][1] = e;
    }
    const D = simpMul(dens.filter(([b]) => !isOne(b)).map(([b, e]) => simpPow(b, e)));
    const numer = simpAdd(parts.map(([n, d]) => expandRec(simpMul([n, D, simpPow(d, NEG_ONE)]))));
    return simpMul([numer, simpPow(D, NEG_ONE)]);
  } finally { CTX = prev; }
}

export { UNDEF, OO, I, PI, E };
