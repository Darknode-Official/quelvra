// Quelvra series engine: truncated generalized power series (Taylor / Laurent / Puiseux) with
// exact coefficients, built by recursive series arithmetic.
//
// A series in t (t -> 0+) is { terms: [{ e: Rational, c: tree }], ord: Rational | null }:
//   sum c_i t^(e_i) + O(t^ord), exponents strictly increasing, ord === null means exact.
// Coefficients are trees free of t. They may contain the symbol __L, which stands for ln(t)
// (a slowly varying factor: t^a (ln t)^k is ordered first by a); callers substitute it.
//
// Public API
//   seriesTree(u, x, a, n, {dir})  -> { tree (with O-term), terms, ord, point } truncated below order n
//   series(u, t, n, opts)          -> raw series of u in t (t -> 0+) valid to absolute order >= n
//   leading(u, t, opts)            -> { e, c, series } leading term of u as t -> 0+ (c provably nonzero)
//   verifySeries(u, x, a, result)  -> contract-style verification by numeric comparison near a
//
// Every leading-coefficient decision uses isZeroStrong (exact, then high-precision numeric);
// undecidable cases throw instead of guessing.

import { X, N, simp, tidy, qerr, Budget, isZeroStrong, constSign, hp, log10Abs, R } from "./cutil.js";
import { diff } from "./diff.js";
import { coefficients } from "../poly.js";

export const LSYM = X.sym("__L");
const Rz = N.ZERO;
const rk = (r) => `${r.n}/${r.d}`;

// ---------------------------------------------------------------- basic constructors
const mkS = (terms, ord) => ({ terms, ord });
export const sConst = (c) => (c === X.ZERO ? mkS([], null) : mkS([{ e: Rz, c }], null));
export const sMonomial = (c, e) => (c === X.ZERO ? mkS([], null) : mkS([{ e, c }], null));
const ordMin = (a, b) => (a === null ? b : b === null ? a : N.cmp(a, b) <= 0 ? a : b);

function normTerms(list, ord) {
  // merge equal exponents, drop exact zeros and terms at/after ord
  const m = new Map();
  for (const t of list) {
    if (ord !== null && N.cmp(t.e, ord) >= 0) continue;
    const k = rk(t.e);
    const cur = m.get(k);
    if (cur) cur.cs.push(t.c); else m.set(k, { e: t.e, cs: [t.c] });
  }
  const out = [];
  for (const { e, cs } of m.values()) {
    const c = cs.length === 1 ? cs[0] : tidy(X.add(...cs));
    if (c !== X.ZERO) out.push({ e, c });
  }
  out.sort((a, b) => N.cmp(a.e, b.e));
  return out;
}
export function sTrunc(s, N_) {
  if (N_ === null) return s;
  const ord = ordMin(s.ord, N_);
  return mkS(s.terms.filter((t) => N.cmp(t.e, ord) < 0), ord);
}
export function sAdd(a, b) {
  const ord = ordMin(a.ord, b.ord);
  return mkS(normTerms([...a.terms, ...b.terms], ord), ord);
}
export function sScale(a, c) {
  if (c === X.ZERO) return mkS([], a.ord);
  if (c === X.ONE) return a;
  return mkS(normTerms(a.terms.map((t) => ({ e: t.e, c: tidy(X.mul(c, t.c)) })), a.ord), a.ord);
}
export const sNeg = (a) => sScale(a, X.NEG_ONE);
export const sSub = (a, b) => sAdd(a, sNeg(b));
export function sShift(a, e) {
  if (N.isZero(e)) return a;
  return mkS(a.terms.map((t) => ({ e: N.add(t.e, e), c: t.c })), a.ord === null ? null : N.add(a.ord, e));
}
const lowOf = (s) => (s.terms.length ? s.terms[0].e : s.ord);

export function sMul(a, b, cap) {
  Budget.check();
  // absolute order of the product: min(ordA + lowB, ordB + lowA) (underestimated lows are safe)
  let ord = null;
  const la = lowOf(a), lb = lowOf(b);
  if (a.ord !== null && lb !== null) ord = ordMin(ord, N.add(a.ord, lb));
  if (b.ord !== null && la !== null) ord = ordMin(ord, N.add(b.ord, la));
  if (a.ord !== null && !b.terms.length && b.ord === null) ord = null; // b exactly zero
  if (!a.terms.length && a.ord === null) return mkS([], null);
  if (!b.terms.length && b.ord === null) return mkS([], null);
  if (cap !== undefined && cap !== null) ord = ordMin(ord, cap);
  const list = [];
  for (const s of a.terms) {
    for (const t of b.terms) {
      const e = N.add(s.e, t.e);
      if (ord !== null && N.cmp(e, ord) >= 0) continue;
      list.push({ e, c: X.mul(s.c, t.c) });
    }
  }
  return mkS(normTerms(list.map((t) => ({ e: t.e, c: t.c })), ord), ord);
}

// Leading term with a provably nonzero coefficient; removes zero terms it proves.
export function strongLead(s, ctx) {
  let i = 0;
  while (i < s.terms.length) {
    Budget.check();
    const t = s.terms[i];
    if (!(ctx.zeroFn ? ctx.zeroFn(t.c) : isZeroStrong(t.c, ctx.special || {}))) return { e: t.e, c: t.c, idx: i };
    i++;
  }
  return null;
}
function needMore() { return qerr("NEEDMORE", "more terms needed"); }

// Split s = c t^e (1 + R); returns { c, e, R } where R has only positive exponents.
function factorLead(s, ctx) {
  const L = strongLead(s, ctx);
  if (!L) throw needMore();
  const inv = simp(X.pow(L.c, X.NEG_ONE));
  const rest = s.terms.slice(L.idx + 1).map((t) => ({ e: N.sub(t.e, L.e), c: tidy(X.mul(t.c, inv)) }));
  const ordR = s.ord === null ? null : N.sub(s.ord, L.e);
  return { c: L.c, e: L.e, R: mkS(normTerms(rest, ordR), ordR) };
}
// sum_{k>=0} a(k) R^k truncated at relative order `target` (R has positive exponents)
function applyPowerSeries(R, coef, target, maxK = 400) {
  const m = R.terms.length ? R.terms[0].e : R.ord;
  let ord = ordMin(target, R.ord);
  const a0 = coef(0);
  let acc = sConst(a0);
  if (m === null || (!R.terms.length && R.ord === null)) return mkS(acc.terms, null); // R == 0 exactly
  if (N.cmp(m, Rz) <= 0) throw qerr("INTERNAL", "power series in a non-small quantity");
  let pk = sConst(X.ONE);
  for (let k = 1; k <= maxK; k++) {
    Budget.check();
    if (ord !== null && N.cmp(N.mul(N.Q(k), m), ord) >= 0) break;
    pk = sMul(pk, R, ord);
    const ak = coef(k);
    if (ak !== X.ZERO) acc = sAdd(acc, sScale(pk, ak));
    if (k === maxK) throw qerr("BUDGET", "series needs too many terms");
  }
  if (ord === null) ord = null;
  return sTrunc(mkS(acc.terms, ord), ord);
}

// ---------------------------------------------------------------- elementary functions of series
function realPowOK(c, p, ctx) {
  // c^p for a nonzero coefficient c in the real domain
  if (X.isInt(p)) return true;
  if (X.isNum(p) && p.v.d % 2n === 1n) return true;
  const s = coeffSign(c, ctx);
  if (s > 0) return true;
  throw qerr("UNDEFINED", "an even root of a negative quantity is not real");
}
export function coeffSign(c, ctx) {
  if (ctx.signFn) return ctx.signFn(c);
  const fs = X.freeSymbols(c);
  if (!fs.size) return constSign(c);
  if (fs.size === 1 && fs.has(LSYM.name)) {
    // polynomial in L = ln t -> -oo: sign of the leading coefficient times (-1)^degree
    const cs = coefficients(c, LSYM.name);
    if (cs && cs.length && cs.every((k) => !X.freeSymbols(k).size)) {
      const d = cs.length - 1;
      return constSign(cs[d]) * (d % 2 ? -1 : 1);
    }
  }
  throw qerr("UNDECIDABLE", "the sign of a coefficient depends on a parameter");
}
export function sPow(s, p, ctx) {
  const { c, e, R } = factorLead(s, ctx);
  const pv = X.isNum(p) ? p.v : null;
  if (!pv && !N.isZero(e)) throw qerr("UNSUPPORTED", "symbolic power of a quantity tending to 0 or infinity");
  realPowOK(c, p, ctx);
  const cp = simp(X.pow(c, p));
  if (cp === X.UNDEF || X.contains(cp, X.I)) throw qerr("UNDEFINED", "power is not real");
  const ep = pv ? N.mul(e, pv) : Rz;
  const target = ctx.N === null ? null : N.sub(ctx.N, ep);
  let body;
  if (pv && pv.d === 1n && pv.n >= 0n && R.ord === null) {
    body = sConst(X.ONE);
    for (let k = 0n; k < pv.n; k++) body = sMul(body, mkS([{ e: Rz, c: X.ONE }, ...R.terms], null), target);
  } else {
    // (1 + R)^p = sum binom(p, k) R^k
    let bc = X.ONE;
    const coefs = [X.ONE];
    body = applyPowerSeries(R, (k) => {
      while (coefs.length <= k) {
        const j = coefs.length - 1;
        bc = simp(X.mul(bc, X.add(p, X.num(-j)), X.num(N.Q(1n, BigInt(j + 1)))));
        coefs.push(bc);
      }
      return coefs[k];
    }, target);
  }
  return sShift(sScale(body, cp), ep);
}
function splitConst(s, ctx) {
  // s = c0 + R with R -> 0; throws when s has (provably) nonzero negative-exponent terms
  let i = 0;
  const terms = s.terms;
  while (i < terms.length && N.cmp(terms[i].e, Rz) < 0) {
    if (!(ctx.zeroFn ? ctx.zeroFn(terms[i].c) : isZeroStrong(terms[i].c, ctx.special || {}))) throw qerr("DIVERGENT", "the argument tends to infinity");
    i++;
  }
  if (s.ord !== null && N.cmp(s.ord, Rz) <= 0) throw needMore();
  let c0 = X.ZERO;
  if (i < terms.length && N.isZero(terms[i].e)) { c0 = terms[i].c; i++; }
  return { c0, R: mkS(terms.slice(i), s.ord) };
}
export function sExp(s, ctx) {
  const { c0, R } = splitConst(s, ctx);
  // e^(alpha ln t + beta) = t^alpha e^beta
  let alpha = Rz, beta = c0;
  if (X.hasSym(c0, LSYM.name)) {
    const cs = coefficients(c0, LSYM.name);
    if (!cs || cs.length !== 2 || !X.isNum(cs[1]) || X.hasSym(cs[0], LSYM.name)) {
      // Gruntz context: ln(omega) is a known function of x that varies slower than omega, so the
      // factor e^(c0) is a coefficient (exact identity after substituting ln(omega))
      if (!ctx.Lval) throw qerr("UNSUPPORTED", "exponential of a logarithmic quantity");
      beta = simp(X.subs(c0, { [LSYM.name]: ctx.Lval }));
    } else {
      alpha = cs[1].v;
      beta = cs[0] || X.ZERO;
    }
  }
  const eb = simp(X.pow(X.E, beta));
  const target = ctx.N === null ? null : N.sub(ctx.N, alpha);
  const facts = [X.ONE];
  const body = applyPowerSeries(R, (k) => {
    while (facts.length <= k) facts.push(X.num(N.Q(1n, N.factorial(facts.length))));
    return facts[k];
  }, target);
  return sShift(sScale(body, eb), alpha);
}
export function sLog(s, ctx) {
  const { c, e, R } = factorLead(s, ctx);
  if (X.hasSym(c, LSYM.name)) {
    if (coeffSign(c, ctx) <= 0) throw qerr("UNDEFINED", "logarithm of a negative quantity");
  } else if (coeffSign(c, ctx) <= 0) throw qerr("UNDEFINED", "logarithm of a negative quantity");
  const head = tidy(X.add(simp(X.fn("ln", c)), X.mul(X.num(e), LSYM)));
  const body = applyPowerSeries(R, (k) => (k === 0 ? X.ZERO : X.num(N.Q(k % 2 ? 1n : -1n, BigInt(k)))), ctx.N);
  return sAdd(sConst(head), body);
}
function sinCosR(R, ctx) {
  const facts = [];
  const f = (k) => { while (facts.length <= k) facts.push(N.factorial(facts.length)); return facts[k]; };
  const sinR = applyPowerSeries(R, (k) => (k % 2 ? X.num(N.Q((k % 4 === 1 ? 1n : -1n), f(k))) : X.ZERO), ctx.N);
  const cosR = applyPowerSeries(R, (k) => (k % 2 ? X.ZERO : X.num(N.Q((k % 4 === 0 ? 1n : -1n), f(k)))), ctx.N);
  return { sinR, cosR };
}
export function sTrig(name, s, ctx) {
  let parts;
  try { parts = splitConst(s, ctx); } catch (e) { if (e.code === "DIVERGENT") throw qerr("OSCILLATES", `${name} of a quantity tending to infinity oscillates`); throw e; }
  const { c0, R } = parts;
  if (X.hasSym(c0, LSYM.name)) throw qerr("UNSUPPORTED", "trigonometric function of a logarithm");
  const { sinR, cosR } = sinCosR(R, ctx);
  const sc = simp(X.fn("sin", c0)), cc = simp(X.fn("cos", c0));
  const sinS = c0 === X.ZERO ? sinR : sAdd(sScale(cosR, sc), sScale(sinR, cc));
  const cosS = c0 === X.ZERO ? cosR : sSub(sScale(cosR, cc), sScale(sinR, sc));
  switch (name) {
    case "sin": return sinS;
    case "cos": return cosS;
    case "tan": return sMul(sinS, sPow(cosS, X.NEG_ONE, ctx), ctx.N);
    case "cot": return sMul(cosS, sPow(sinS, X.NEG_ONE, ctx), ctx.N);
    case "sec": return sPow(cosS, X.NEG_ONE, ctx);
    case "csc": return sPow(sinS, X.NEG_ONE, ctx);
  }
  throw qerr("UNSUPPORTED", name);
}
// f(c0 + R) = sum f^(k)(c0)/k! R^k with the derivatives computed symbolically.
const U = X.sym("__u");
export function sGeneric(name, s, ctx) {
  let parts;
  try { parts = splitConst(s, ctx); } catch (e) { if (e.code === "DIVERGENT") throw qerr("DIVERGENT", `${name} of a quantity tending to infinity`); throw e; }
  const { c0, R } = parts;
  if (X.hasSym(c0, LSYM.name)) throw qerr("UNSUPPORTED", `${name} of a logarithm`);
  let d = X.fn(name, U);
  const vals = [];
  const at = (k) => {
    while (vals.length <= k) {
      Budget.check();
      if (vals.length > 0) d = diff(d, U);
      let v = simp(X.subs(d, { __u: c0 }));
      if (v === X.UNDEF || X.contains(v, X.OO)) throw qerr("SINGULAR", `${name} is not analytic at ${c0 === X.ZERO ? "0" : "this point"}`);
      vals.push(simp(X.mul(v, X.num(N.Q(1n, N.factorial(vals.length))))));
    }
    return vals[k];
  };
  at(0);
  return applyPowerSeries(R, at, ctx.N);
}
export function sAtan(s, ctx) {
  const L = strongLead(s, ctx);
  if (L && N.cmp(L.e, Rz) < 0) {
    // atan(s) = sign(c) pi/2 - atan(1/s)
    const sg = coeffSign(L.c, ctx);
    const inv = sPow(s, X.NEG_ONE, ctx);
    return sSub(sConst(simp(X.mul(X.num(sg), X.HALF, X.PI))), sGeneric("atan", inv, ctx));
  }
  return sGeneric("atan", s, ctx);
}
export function sAbs(s, ctx) {
  const L = strongLead(s, ctx);
  if (!L) throw needMore();
  const sg = coeffSign(L.c, ctx);
  return sg > 0 ? s : sNeg(s);
}

// ---------------------------------------------------------------- tree -> series
const HYPER = {
  sinh: (u) => X.mul(X.HALF, X.add(X.exp(u), X.neg(X.exp(X.neg(u))))),
  cosh: (u) => X.mul(X.HALF, X.add(X.exp(u), X.exp(X.neg(u)))),
  tanh: (u) => X.mul(X.add(X.exp(u), X.neg(X.exp(X.neg(u)))), X.pow(X.add(X.exp(u), X.exp(X.neg(u))), X.NEG_ONE)),
  coth: (u) => X.mul(X.add(X.exp(u), X.exp(X.neg(u))), X.pow(X.add(X.exp(u), X.neg(X.exp(X.neg(u)))), X.NEG_ONE)),
  sech: (u) => X.mul(X.TWO, X.pow(X.add(X.exp(u), X.exp(X.neg(u))), X.NEG_ONE)),
  csch: (u) => X.mul(X.TWO, X.pow(X.add(X.exp(u), X.neg(X.exp(X.neg(u)))), X.NEG_ONE)),
};
function ser(u, ctx) {
  const hit = ctx.memo.get(u);
  if (hit) return hit;
  Budget.check();
  const r = ser1(u, ctx);
  ctx.memo.set(u, r);
  return r;
}
function ser1(u, ctx) {
  const t = ctx.t;
  if (!X.hasSym(u, t.name)) {
    if (u === X.UNDEF || X.contains(u, X.OO)) throw qerr("UNDEFINED", "undefined sub-expression");
    return sConst(u);
  }
  switch (u.k) {
    case "sym": return sMonomial(X.ONE, N.ONE);
    case "add": {
      let acc = mkS([], null);
      for (const a of u.args) acc = sAdd(acc, ser(a, ctx));
      return sTrunc(acc, ctx.N);
    }
    case "mul": {
      // multiply the most negative-order factors last for better truncation
      let acc = sConst(X.ONE);
      for (const a of u.args) acc = sMul(acc, ser(a, ctx), ctx.N);
      return acc;
    }
    case "pow": {
      const [b, e] = u.args;
      if (!X.hasSym(e, t.name)) {
        if (b === X.E) return sConst(u);
        return sPow(ser(b, ctx), e, ctx);
      }
      if (b === X.E) return sExp(ser(e, ctx), ctx);
      return sExp(ser(simp(X.mul(e, X.fn("ln", b))), ctx), ctx);
    }
    case "fn": {
      const n = u.name, a = u.args[0];
      if (n === "ln") return sLog(ser(a, ctx), ctx);
      if (n === "log") {
        if (u.args.length === 2) return ser(simp(X.mul(X.fn("ln", u.args[1]), X.pow(X.fn("ln", u.args[0]), X.NEG_ONE))), ctx);
        return ser(simp(X.mul(X.fn("ln", a), X.pow(X.fn("ln", X.num(10)), X.NEG_ONE))), ctx);
      }
      if (n === "exp") return sExp(ser(a, ctx), ctx);
      if (["sin", "cos", "tan", "cot", "sec", "csc"].includes(n)) return sTrig(n, ser(a, ctx), ctx);
      if (HYPER[n]) return ser(simp(HYPER[n](a)), ctx);
      if (n === "atan") return sAtan(ser(a, ctx), ctx);
      if (n === "acot") return sSub(sConst(simp(X.mul(X.HALF, X.PI))), sAtan(ser(a, ctx), ctx));
      if (n === "abs") return sAbs(ser(a, ctx), ctx);
      if (n === "sqrt") return sPow(ser(a, ctx), X.HALF, ctx);
      if (n === "factorial") return sGeneric("gamma", ser(simp(X.add(a, X.ONE)), ctx), ctx);
      if (["asin", "acos", "asinh", "acosh", "atanh", "erf", "gamma"].includes(n) && u.args.length === 1) return sGeneric(n, ser(a, ctx), ctx);
      throw qerr("UNSUPPORTED", `no series rule for ${n}`);
    }
    default:
      throw qerr("UNSUPPORTED", `no series rule for ${u.k}`);
  }
}

// series of u (tree in t) to absolute order >= n (Rational or number); retries with more terms.
export function series(u, t, n, opts = {}) {
  const ts = typeof t === "string" ? X.sym(t) : t;
  const target = typeof n === "number" ? N.Q(n) : n;
  let lastErr = null;
  for (const extra of [0, 2, 4, 8, 14, 22]) {
    const ctx = { t: ts, N: N.add(target, N.Q(extra)), memo: new Map(), special: opts.special || {}, signFn: opts.signFn || null, zeroFn: opts.zeroFn || null, Lval: opts.Lval || null };
    try {
      const s = ser(u, ctx);
      if (s.ord === null || N.cmp(s.ord, target) >= 0) return sTrunc(s, target);
      lastErr = null;
    } catch (e) {
      if (e.code !== "NEEDMORE") throw e;
      lastErr = e;
    }
  }
  throw lastErr || qerr("NEEDMORE", "could not reach the requested order");
}
// Leading term of u as t -> 0+: { e, c } with c provably nonzero (c may contain __L).
export function leading(u, t, opts = {}) {
  const ts = typeof t === "string" ? X.sym(t) : t;
  const special = { [LSYM.name]: [-3.7, -9.1, -17.3, -31.9], ...(opts.special || {}) };
  let lastErr = null;
  for (const n of [1, 2, 4, 6, 9, 13, 18, 26]) {
    Budget.hard();
    const ctx = { t: ts, N: N.Q(n), memo: new Map(), special, signFn: opts.signFn || null, zeroFn: opts.zeroFn || null, Lval: opts.Lval || null };
    let s;
    try { s = ser(u, ctx); } catch (e) { if (e.code !== "NEEDMORE") throw e; lastErr = e; continue; }
    if (!s.terms.length && s.ord === null) return { e: null, c: X.ZERO, zero: true, series: s };
    const L = strongLead(s, ctx);
    if (L && (s.ord === null || N.cmp(L.e, s.ord) < 0)) return { e: L.e, c: simp(L.c), series: s };
    if (!L && s.ord === null) return { e: null, c: X.ZERO, zero: true, series: s };
  }
  throw lastErr || qerr("NEEDMORE", "the leading term could not be determined (too much cancellation)");
}

// ---------------------------------------------------------------- the series command
// seriesTree(u, x, a, n): expansion of u about x = a (a may be OO or -OO) with terms of order < n
// in (x - a) (or in 1/x at infinity), plus an O-term. dir "-" expands on the left (Puiseux terms
// use |x - a|).
export function seriesTree(u, x, a, n, opts = {}) {
  const xs = typeof x === "string" ? X.sym(x) : x;
  const T = X.sym("__t");
  const inf = a === X.OO || (a.k === "mul" && a.args.includes(X.OO));
  const negInf = inf && a !== X.OO;
  const left = opts.dir === "-";
  let sub;
  if (inf) sub = negInf ? X.neg(X.pow(T, X.NEG_ONE)) : X.pow(T, X.NEG_ONE);
  else sub = left ? X.sub(a, T) : X.add(a, T);
  const v = simp(X.subs(simp(u), { [xs.name]: sub }));
  const order = typeof n === "number" ? N.Q(n) : X.isNum(n) ? n.v : n;
  const s = series(v, T, order, opts);
  // back-substitute t
  let tback, lnback;
  if (inf) { tback = negInf ? X.neg(X.pow(xs, X.NEG_ONE)) : X.pow(xs, X.NEG_ONE); lnback = negInf ? X.neg(X.fn("ln", X.neg(xs))) : X.neg(X.fn("ln", xs)); }
  else { tback = left ? X.sub(a, xs) : X.sub(xs, a); lnback = X.fn("ln", tback); }
  const termTrees = s.terms.map((tm) => simp(X.mul(X.subs(tm.c, { __L: lnback }), X.pow(tback, X.num(tm.e)))));
  const main = simp(X.add(...termTrees));
  const Oterm = s.ord === null ? null : X.fn("O", simp(X.pow(tback, X.num(s.ord))));
  const tree = Oterm ? X.add(main, Oterm) : main;
  return { tree, main, O: Oterm, terms: s.terms.map((tm) => ({ e: tm.e, c: X.subs(tm.c, { __L: lnback }) })), ord: s.ord, point: a, variable: xs, tback };
}

// Numeric verification: |f(x) - S(x)| must shrink like |x - a|^ord near a.
export function verifySeries(u, x, a, res) {
  const xs = typeof x === "string" ? x : x.name;
  const inf = a === X.OO || (a.k === "mul" && a.args.includes(X.OO));
  const checks = [];
  const params = [...X.freeSymbols(u)].filter((v) => v !== xs);
  const penv = {};
  params.forEach((p, i) => { penv[p] = 0.61 + 0.37 * i; });
  const aval = inf ? 0 : hp(a, {}, { digits: 30 });
  if (!inf && !aval.ok) return { status: "inconclusive", checks: [{ kind: "series-numeric", ok: null, detail: "could not evaluate the expansion point" }] };
  const hs = [1e-2, 1e-3, 1e-4, 1e-5];
  const errs = [];
  for (const h of hs) {
    const xv = inf ? (a === X.OO ? 1 / h : -1 / h) : aval.re + (res.dir === "-" ? -h : h);
    const env = { ...penv, [xs]: xv };
    const f = hp(u, env, { digits: 60, maxDigits: 400 });
    const sv = hp(res.main, env, { digits: 60, maxDigits: 400 });
    if (!f.ok || !sv.ok) { errs.push(null); continue; }
    const d = hp(X.sub(u, res.main), env, { digits: 80, maxDigits: 600 });
    errs.push(d.ok ? Math.max(log10Abs(d.big), d.bigIm ? log10Abs(d.bigIm) : -Infinity) : null);
  }
  const good = errs.map((e, i) => [e, Math.log10(hs[i])]).filter(([e]) => e !== null);
  if (good.length < 2) return { status: "inconclusive", checks: [{ kind: "series-numeric", ok: null, detail: "the function could not be evaluated near the point" }] };
  if (res.ord === null) {
    const ok = good.every(([e]) => e < -25);
    checks.push({ kind: "series-numeric", ok, detail: ok ? "the expansion is exact: it equals the function at test points" : "the exact expansion differs from the function" });
    return { status: ok ? "verified-numeric" : "failed", checks };
  }
  const ord = N.toFloat(res.ord);
  // slope of log|error| against log h must be at least about ord (log factors allow slack)
  let ok = true, detail = "";
  for (let i = 1; i < good.length; i++) {
    const [e1, l1] = good[i - 1], [e2, l2] = good[i];
    if (e2 === -Infinity) continue;
    const slope = (e2 - e1) / (l2 - l1);
    if (e1 !== -Infinity && slope < ord - 0.35 && e2 > -30) { ok = false; detail = `error decays like h^${slope.toFixed(2)}, expected h^${ord}`; }
  }
  checks.push({ kind: "series-numeric", ok, detail: ok ? `the error f - series shrinks like (x - a)^${toTextOrd(res.ord)} at ${good.length} test points` : detail });
  return { status: ok ? "verified-numeric" : "failed", checks };
}
const toTextOrd = (r) => (r.d === 1n ? r.n.toString() : `${r.n}/${r.d}`);
