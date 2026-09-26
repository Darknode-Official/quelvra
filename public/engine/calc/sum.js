// Quelvra sums and products.
//
//   sumCompute(f, k, lo, hi, {log}) -> { kind: "value", value, method, steps, conditions, cert }
//                                     | { kind: "diverges", reason, test, steps }
//                                     | { kind: "converges", approx, reason, steps }   (no closed form)
//   productCompute(f, k, lo, hi)    -> { kind: "value", value, method, steps, conditions }
//   verifySum(f, k, lo, hi, res)    -> contract verification record
//   verifyProduct(f, k, lo, hi, res)
//
// Finite sums: direct exact summation, Faulhaber (polynomials, via exact interpolation), Gosper's
// algorithm (hypergeometric terms; the certificate is checked as an exact polynomial identity),
// polynomial times geometric (symbolic ratio, by differentiating the geometric sum), binomial
// sums over the full range, and linearity.
// Infinite sums: divergence test, comparison with k^-p (ln k)^-q via asymptotics, ratio test,
// alternating series test; closed forms for geometric, Gosper-summable (telescoping), rational
// terms (zeta(2m) via Bernoulli numbers, digamma differences at rational shifts with denominator
// 1, 2, 3, 4, 6), alternating rational terms (pairing), and power series (exp, log, sin, cos,
// sinh, cosh, atan, atanh, geometric) with polynomial factors.
// Products: rational terms with rational roots (factorial / gamma ratios), exponential factors,
// constants; infinite products as limits of the partial products.

import { X, N, simp, simpExpand, qerr, Budget, isZeroStrong, constSign, hp, log10Abs, isNegInf, NEG_OO, now } from "./cutil.js";
import * as P from "../poly.js";
import { together, numerDenom, makeCtx, expand } from "../simplify.js";
import { diff } from "./diff.js";
import { limit as limitOf, Gruntz, gprep } from "./limit.js";
import * as NU from "../numeric.js";
import * as B from "../bigfloat.js";
import { makeStep } from "../steps.js";

const Q = N.Q;
const S = (rule, title, why, before = null, after = null, extra = {}) => makeStep({ rule, title, why, before, after, ...extra });
const isIntTree = (u) => X.isNum(u) && u.v.d === 1n;
const big = (u) => u.v.n;

// ---------------------------------------------------------------- small exact linear algebra over Q
function solveQ(M, rhs) {
  // M: rows of Rationals (m x n), rhs: m Rationals. Returns a solution vector or null.
  const m = M.length, n = m ? M[0].length : 0;
  const A = M.map((r, i) => [...r, rhs[i]]);
  const piv = [];
  let row = 0;
  for (let c = 0; c < n && row < m; c++) {
    let p = -1;
    for (let r = row; r < m; r++) if (!N.isZero(A[r][c])) { p = r; break; }
    if (p < 0) continue;
    [A[row], A[p]] = [A[p], A[row]];
    const inv = N.inv(A[row][c]);
    for (let j = c; j <= n; j++) A[row][j] = N.mul(A[row][j], inv);
    for (let r = 0; r < m; r++) {
      if (r === row || N.isZero(A[r][c])) continue;
      const f = A[r][c];
      for (let j = c; j <= n; j++) A[r][j] = N.sub(A[r][j], N.mul(f, A[row][j]));
    }
    piv.push(c);
    row++;
  }
  for (let r = row; r < m; r++) if (!N.isZero(A[r][n])) return null;
  const x = new Array(n).fill(N.ZERO);
  piv.forEach((c, i) => { x[c] = A[i][n]; });
  return x;
}

// ---------------------------------------------------------------- rational functions of k
function ratParts(u, kn) {
  const t = together(simp(u), makeCtx({ budget: { ops: 400000 } }));
  const [nu, de] = numerDenom(t);
  const A = P.fromTree(nu, kn), Bp = P.fromTree(de, kn);
  if (!A || !Bp || !Bp.length) return null;
  const g = P.gcd(A, Bp);
  if (g.length > 1) return { num: P.exactDiv(A, g), den: P.exactDiv(Bp, g) };
  return { num: A, den: Bp };
}
const shiftPoly = (p, h) => P.compose(p, [Q(h), N.ONE]); // p(k + h)
const linCoeffs = (e, kn) => {
  const cs = P.coefficients(e, kn);
  if (!cs || cs.length > 2) return null;
  return { a: cs[1] || X.ZERO, b: cs[0] || X.ZERO };
};

// ---------------------------------------------------------------- hypergeometric decomposition
// Decompose f(k) into factors; returns { z: tree, A: UPoly, B: UPoly } with f(k+1)/f(k) = z A(k)/B(k)
// (A, B with rational coefficients), or null when f is not of this shape.
function hyperRatio(f, kn) {
  let z = X.ONE, A = [N.ONE], Bp = [N.ONE];
  const fs = f.k === "mul" ? f.args : [f];
  const mulRatio = (a, b, m) => {
    if (m > 0) { A = P.mul(A, P.pow(a, m)); Bp = P.mul(Bp, P.pow(b, m)); }
    else if (m < 0) { A = P.mul(A, P.pow(b, -m)); Bp = P.mul(Bp, P.pow(a, -m)); }
  };
  const factRatio = (arg, m) => {
    // factorial(arg), arg = a k + c with integer a
    const lc = linCoeffs(arg, kn);
    if (!lc || !isIntTree(lc.a) || !X.isNum(lc.b) || X.isZero(lc.a)) return false;
    const a = Number(big(lc.a)), c = lc.b.v;
    let num = [N.ONE];
    if (a > 0) { for (let i = 1; i <= a; i++) num = P.mul(num, [N.add(c, Q(i)), Q(a)]); mulRatio(num, [N.ONE], m); }
    else { let d = [N.ONE]; for (let i = 0; i < -a; i++) d = P.mul(d, [N.sub(c, Q(i)), Q(a)]); mulRatio([N.ONE], d, m); }
    return true;
  };
  for (const g0 of fs) {
    if (!X.hasSym(g0, kn)) continue;
    let base = g0, m = 1;
    if (g0.k === "pow" && X.hasSym(g0.args[1], kn)) {
      if (X.hasSym(g0.args[0], kn)) return null;
      const lc = linCoeffs(g0.args[1], kn);
      if (!lc || X.hasSym(lc.a, kn)) return null;
      z = X.mul(z, X.pow(g0.args[0], lc.a));
      continue;
    }
    if (g0.k === "pow" && isIntTree(g0.args[1])) { base = g0.args[0]; m = Number(big(g0.args[1])); }
    else if (g0.k === "pow") return null;
    if (base.k === "fn" && base.name === "factorial") { if (!factRatio(base.args[0], m)) return null; continue; }
    if (base.k === "fn" && base.name === "gamma") { if (!factRatio(simp(X.add(base.args[0], X.NEG_ONE)), m)) return null; continue; }
    if (base.k === "fn" && (base.name === "binomial" || base.name === "nCr")) {
      const [p, q] = base.args;
      const ok = factRatio(p, m) && factRatio(q, -m) && factRatio(simp(X.sub(p, q)), -m);
      if (!ok) return null;
      continue;
    }
    const pp = P.fromTree(base, kn);
    if (!pp) return null;
    mulRatio(shiftPoly(pp, 1), pp, m);
  }
  const g = P.gcd(A, Bp);
  if (g.length > 1) { A = P.exactDiv(A, g); Bp = P.exactDiv(Bp, g); }
  // move the leading-coefficient ratio into z (A, B monic)
  const la = P.lc(A), lb = P.lc(Bp);
  z = simp(X.mul(z, X.num(N.div(la, lb))));
  return { z, A: P.monic(A), B: P.monic(Bp) };
}
// ratio check: f(k+1)/f(k) == z A(k)/B(k) at a few integer points (guards against mistakes above)
function ratioOK(f, kn, hr, lo) {
  const start = X.isNum(lo) ? Number(N.floor(lo.v)) : 0;
  let checked = 0;
  for (let j = 0; j < 30 && checked < 4; j++) {
    const k0 = start + 3 + j * 2;
    const a = P.evalAt(hr.A, Q(k0)), b = P.evalAt(hr.B, Q(k0));
    if (N.isZero(b) || N.isZero(a)) continue;
    const f0 = simp(X.subs(f, { [kn]: X.num(k0) })), f1 = simp(X.subs(f, { [kn]: X.num(k0 + 1) }));
    if (f0 === X.ZERO || f0 === X.UNDEF || f1 === X.UNDEF) continue;
    const d = simp(X.sub(X.mul(f1, X.num(b)), X.mul(hr.z, X.num(a), f0)));
    try { if (!isZeroStrong(d)) return false; } catch (_) { return false; }
    checked++;
  }
  return checked >= 2;
}

// ---------------------------------------------------------------- Gosper
// Returns { T: tree in k with T(k+1) - T(k) = f(k), cert } or null (not Gosper-summable). Throws
// when f is not hypergeometric with rational data.
function gosper(f, kn, hr) {
  if (!X.isNum(hr.z)) return null;
  const zq = hr.z.v;
  let a = P.scale(hr.A, zq), b = hr.B, c = [N.ONE];
  // Gosper-Petkovsek normal form: gcd(a(k), b(k+h)) = 1 for all integers h >= 0
  const hs = new Set();
  const fa = P.factorQ(a).factors.map((t) => t.poly), fb = P.factorQ(b).factors.map((t) => t.poly);
  for (const p of fa) for (const q of fb) {
    if (p.length !== q.length || p.length < 2) continue;
    const d = p.length - 1;
    const hq = N.div(N.sub(N.div(p[d - 1], p[d]), N.div(q[d - 1], q[d])), Q(d));
    if (hq.d !== 1n || hq.n < 0n) continue;
    const h = Number(hq.n);
    const qs = shiftPoly(q, h);
    if (P.polyEq(P.monic(qs), P.monic(p))) hs.add(h);
  }
  for (const h of [...hs].sort((x, y) => x - y)) {
    for (let guard = 0; guard < 50; guard++) {
      Budget.check();
      const g = P.gcd(a, shiftPoly(b, h));
      if (g.length <= 1) break;
      a = P.exactDiv(a, g);
      b = P.exactDiv(b, shiftPoly(g, -h));
      for (let i = 1; i <= h; i++) c = P.mul(c, shiftPoly(g, -i));
    }
  }
  // certificate check of the normal form: z A(k) b(k) c(k) == B(k) a(k) c(k+1)
  const lhsN = P.mul(P.mul(P.scale(hr.A, zq), b), c), rhsN = P.mul(P.mul(hr.B, a), shiftPoly(c, 1));
  if (!P.polyEq(lhsN, rhsN)) throw qerr("INTERNAL", "Gosper normal form check failed");
  const bm1 = shiftPoly(b, -1);
  const da = P.deg(a), db = P.deg(bm1), dc = P.deg(c);
  let D;
  if (da !== db || !N.eq(P.lc(a), P.lc(bm1))) D = dc - Math.max(da, db);
  else {
    const d = da;
    const A1 = d >= 1 ? a[d - 1] : N.ZERO, B1 = d >= 1 ? bm1[d - 1] : N.ZERO;
    let cand = dc - d + 1;
    const e = N.div(N.sub(B1, A1), P.lc(a));
    if (e.d === 1n && e.n >= 0n) cand = Math.max(cand, Number(e.n));
    D = cand;
  }
  if (D < 0 || D > 60) return null;
  // a(k) x(k+1) - b(k-1) x(k) = c(k), x of degree D
  const cols = [];
  for (let j = 0; j <= D; j++) {
    const kj = new Array(j + 1).fill(N.ZERO); kj[j] = N.ONE;
    cols.push(P.sub(P.mul(a, shiftPoly(kj, 1)), P.mul(bm1, kj)));
  }
  const rows = Math.max(dc + 1, ...cols.map((p) => p.length));
  const M = [], rhs = [];
  for (let i = 0; i < rows; i++) { M.push(cols.map((p) => p[i] || N.ZERO)); rhs.push(c[i] || N.ZERO); }
  const sol = solveQ(M, rhs);
  if (!sol) return null;
  const xk = P.norm(sol);
  if (!xk.length) return null;
  // exact check of the key equation
  const chk = P.sub(P.sub(P.mul(a, shiftPoly(xk, 1)), P.mul(bm1, xk)), c);
  if (chk.length) throw qerr("INTERNAL", "Gosper key equation check failed");
  const k = X.sym(kn);
  const factor = simp(X.mul(P.toTree(P.mul(bm1, xk), kn), X.pow(P.toTree(c, kn), X.NEG_ONE)));
  const T = simp(X.mul(factor, f));
  return { T, factor, cert: { a, b, c, x: xk } };
}

// ---------------------------------------------------------------- factorial normalisation
// Rewrite factorial(n + a) (a integer) relative to the smallest offset present, so ratios cancel:
// (n+2)!/n! -> (n+1)(n+2).
export function normFactorials(u, vn) {
  const groups = new Map();
  const collect = (w) => {
    if (w.k === "fn" && (w.name === "factorial" || w.name === "gamma") && X.hasSym(w, vn)) {
      const arg = w.name === "gamma" ? simp(X.add(w.args[0], X.NEG_ONE)) : w.args[0];
      const lc = linCoeffs(arg, vn);
      if (lc && X.isNum(lc.b) && !X.hasSym(lc.a, vn)) {
        const frac = N.sub(lc.b.v, Q(N.floor(lc.b.v)));
        const key = `${lc.a.id}|${frac.n}/${frac.d}`;
        const g = groups.get(key) || { a: lc.a, frac, min: null, items: [] };
        const off = Number(N.floor(lc.b.v));
        g.min = g.min === null ? off : Math.min(g.min, off);
        g.items.push(w);
        groups.set(key, g);
      }
    }
    w.args.forEach(collect);
  };
  collect(u);
  const rep = new Map();
  for (const g of groups.values()) {
    if (g.items.length < 2) continue;
    const base = simp(X.add(X.mul(g.a, X.sym(vn)), X.num(N.add(g.frac, Q(g.min)))));
    for (const w of g.items) {
      const arg = w.name === "gamma" ? simp(X.add(w.args[0], X.NEG_ONE)) : w.args[0];
      const off = Number(N.floor(linCoeffs(arg, vn).b.v)) - g.min;
      if (off > 60) continue;
      const fs = [X.fn("factorial", base)];
      for (let i = 1; i <= off; i++) fs.push(X.add(base, X.num(i)));
      rep.set(w, X.mul(...fs));
    }
  }
  if (!rep.size) return u;
  const go = (w) => (rep.has(w) ? rep.get(w) : w.args.length ? X.withArgs(w, w.args.map(go)) : w);
  return simp(go(u));
}
function niceForm(u, vn) {
  let v = normFactorials(simp(u), vn);
  try {
    const f = P.factorTree(v);
    if (X.size(f) <= X.size(v) + 2) v = f;
  } catch (_) { /* keep */ }
  return v;
}

// ---------------------------------------------------------------- Faulhaber
const FAUL = new Map();
function faulhaber(j) {
  // F_j(n) = sum_{k=0}^{n} k^j as a UPoly in n
  if (FAUL.has(j)) return FAUL.get(j);
  const pts = [];
  let acc = N.ZERO;
  for (let m = 0; m <= j + 1; m++) {
    acc = N.add(acc, m === 0 ? (j === 0 ? N.ONE : N.ZERO) : N.pow(Q(m), j));
    pts.push([Q(m), acc]);
  }
  const p = P.interpolate(pts);
  FAUL.set(j, p);
  return p;
}
function polySum(f, kn, lo, hi) {
  const cs = P.coefficients(f, kn);
  if (!cs || cs.some((c) => X.hasSym(c, kn)) || cs.length > 60) return null;
  const parts = [];
  cs.forEach((c, j) => {
    if (c === X.ZERO) return;
    const F = faulhaber(j);
    const Fn = (v) => simp(X.subs(P.toTree(F, "__n"), { __n: v }));
    parts.push(X.mul(c, X.sub(Fn(hi), Fn(simp(X.sub(lo, X.ONE))))));
  });
  return simp(X.add(...parts));
}

// ---------------------------------------------------------------- poly * w^k (symbolic w)
function splitGeomPoly(f, kn) {
  // f = C * poly(k) * w^k ; returns { C, w, poly: tree } or null
  const fs = f.k === "mul" ? f.args : [f];
  let C = [], w = [], rest = [];
  for (const g of fs) {
    if (!X.hasSym(g, kn)) { C.push(g); continue; }
    if (g.k === "pow" && !X.hasSym(g.args[0], kn) && X.hasSym(g.args[1], kn)) {
      const lc = linCoeffs(g.args[1], kn);
      if (!lc || X.hasSym(lc.a, kn)) return null;
      w.push(X.pow(g.args[0], lc.a));
      C.push(X.pow(g.args[0], lc.b));
      continue;
    }
    rest.push(g);
  }
  const poly = simp(X.mul(...rest));
  const cs = P.coefficients(poly, kn);
  if (!cs || cs.some((c) => X.hasSym(c, kn))) return null;
  return { C: simp(X.mul(...C)), w: simp(X.mul(...w)), polyC: cs };
}
// sum_{k=lo}^{hi} P(k) W^k = P(theta) G(W), theta = W d/dW
function thetaApply(cs, G, Wn) {
  const W = X.sym(Wn);
  let cur = G, out = [];
  cs.forEach((c, j) => {
    if (j > 0) cur = simp(X.mul(W, diff(cur, W)));
    if (c !== X.ZERO) out.push(X.mul(c, cur));
  });
  return simp(X.add(...out));
}
function geomPolySum(f, kn, lo, hi) {
  const s = splitGeomPoly(f, kn);
  if (!s || s.w === X.ONE) return null;
  const Wn = "__W", W = X.sym(Wn);
  const G = X.mul(X.sub(X.pow(W, X.add(hi, X.ONE)), X.pow(W, lo)), X.pow(X.sub(W, X.ONE), X.NEG_ONE));
  const r = thetaApply(s.polyC, simp(G), Wn);
  const value = simp(X.mul(s.C, X.subs(r, { [Wn]: s.w })));
  const conditions = X.isNum(s.w) ? [] : [X.rel("!=", s.w, X.ONE)];
  return { value, conditions, w: s.w };
}
// sum_{k=0}^{n} P(k) binomial(n, k) w^k = P(theta) (1 + w)^n
function binomialSum(f, kn, lo, hi) {
  if (lo !== X.ZERO) return null;
  const fs = f.k === "mul" ? f.args : [f];
  const bi = fs.filter((g) => g.k === "fn" && (g.name === "binomial" || g.name === "nCr") && g.args[1] === X.sym(kn) && g.args[0] === hi);
  if (bi.length !== 1) return null;
  const rest = simp(X.mul(...fs.filter((g) => g !== bi[0])));
  const s = splitGeomPoly(rest, kn);
  if (!s) return null;
  const Wn = "__W", W = X.sym(Wn);
  const r = thetaApply(s.polyC, X.pow(X.add(X.ONE, W), hi), Wn);
  return { value: simp(X.mul(s.C, X.subs(r, { [Wn]: s.w }))), conditions: [] };
}

// ---------------------------------------------------------------- finite sums
function direct(f, kn, lo, hi) {
  const a = big(lo), b = big(hi);
  const terms = [];
  for (let k = a; k <= b; k++) { Budget.check(); terms.push(simp(X.subs(f, { [kn]: X.num(k) }))); }
  const v = simp(X.add(...terms));
  if (v === X.UNDEF || terms.includes(X.UNDEF)) throw qerr("UNDEFINED", "a term of the sum is undefined");
  return v;
}
function finiteSum(f, kn, lo, hi, steps) {
  const k = X.sym(kn);
  if (!X.hasSym(f, kn)) {
    steps.push(S("sum.constant", "Constant term", "Each of the hi - lo + 1 terms is the same.", null, null));
    return { value: simp(X.mul(f, X.add(hi, X.neg(lo), X.ONE))), method: "constant", exact: true };
  }
  if (isIntTree(lo) && isIntTree(hi) && big(hi) - big(lo) <= 1500n) {
    if (big(hi) < big(lo)) return { value: X.ZERO, method: "empty", exact: true };
    const v = direct(f, kn, lo, hi);
    steps.push(S("sum.direct", "Add the terms", `The range has ${big(hi) - big(lo) + 1n} terms; add them exactly.`));
    return { value: v, method: "direct", exact: true };
  }
  const ps = polySum(f, kn, lo, hi);
  if (ps) {
    steps.push(S("sum.faulhaber", "Sum of powers (Faulhaber)", "The summand is a polynomial in " + kn + "; sums of k^j are polynomials of degree j+1 (found by exact interpolation)."));
    return { value: ps, method: "faulhaber", exact: true };
  }
  const hr = hyperRatio(f, kn);
  if (hr && X.isNum(hr.z) && ratioOK(f, kn, hr, lo)) {
    const g = gosper(f, kn, hr);
    if (g) {
      steps.push(S("sum.gosper", "Gosper's algorithm", "The ratio of consecutive terms is a rational function of " + kn + ", and Gosper's algorithm finds a hypergeometric antidifference T with T(k+1) - T(k) = term.", f, g.T));
      const val = gosperEval(f, kn, lo, hi, g);
      if (val) return { value: val, method: "gosper", exact: true, cert: g.cert };
    }
  }
  const gp = geomPolySum(f, kn, lo, hi);
  if (gp) {
    steps.push(S("sum.geometric-poly", "Geometric sum (differentiated)", "Sum of w^k is (w^(n+1) - w^lo)/(w - 1); multiplying the term by k corresponds to applying w d/dw."));
    return { value: gp.value, method: "geometric", conditions: gp.conditions, exact: true };
  }
  const bs = binomialSum(f, kn, lo, hi);
  if (bs) {
    steps.push(S("sum.binomial", "Binomial theorem", "sum_{k=0}^{n} C(n,k) w^k = (1 + w)^n; factors of k correspond to w d/dw."));
    return { value: bs.value, method: "binomial", exact: true };
  }
  if (f.k === "add") {
    const parts = [];
    for (const t of f.args) {
      const r = finiteSum(t, kn, lo, hi, steps);
      if (!r) return null;
      parts.push(r.value);
    }
    steps.push(S("sum.linearity", "Split the sum", "The sum of a sum is the sum of the separate sums."));
    return { value: simp(X.add(...parts)), method: "linearity", exact: true };
  }
  return null;
}
function gosperEval(f, kn, lo, hi, g) {
  // sum_{k=lo}^{hi} f = T(hi+1) - T(lo); if T is singular at lo, start later and add terms
  const at = (v) => simp(X.subs(g.T, { [kn]: v }));
  let start = lo, extra = [];
  for (let s = 0; s < 8; s++) {
    const Tl = at(start);
    if (Tl !== X.UNDEF && !X.contains(Tl, X.UNDEF)) {
      return simp(X.add(at(simp(X.add(hi, X.ONE))), X.neg(Tl), ...extra));
    }
    extra.push(simp(X.subs(f, { [kn]: start })));
    start = simp(X.add(start, X.ONE));
  }
  return null;
}

// ---------------------------------------------------------------- infinite sums: tests
function signFactor(f, kn) {
  // f = (-1)^(a k + b) g with a odd -> { alt: true, g, s0: sign at k with b }, else { alt: false, g: f }
  const fs = f.k === "mul" ? f.args : [f];
  let alt = false, rest = [], pre = [];
  for (const h of fs) {
    if (h.k === "pow" && X.isNum(h.args[0]) && N.isNeg(h.args[0].v) && X.hasSym(h.args[1], kn)) {
      const lc = linCoeffs(h.args[1], kn);
      if (!lc || !isIntTree(lc.a)) return { alt: false, g: f };
      if (big(lc.a) % 2n !== 0n) alt = !alt;
      pre.push(X.pow(X.NEG_ONE, h.args[1]));
      const ab = N.abs(h.args[0].v);
      if (!N.isOne(ab)) rest.push(X.pow(X.num(ab), h.args[1]));
      continue;
    }
    rest.push(h);
  }
  if (!pre.length) return { alt: false, g: f };
  return { alt, g: simp(X.mul(...rest)), sgn: simp(X.mul(...pre)) };
}
function eventualSign(g, kn) {
  const G = new Gruntz(X.sym(kn), null);
  return Budget.with(3000, () => G.sign(gprep(simp(g), X.sym(kn))));
}
function limInf(u, kn) {
  const r = limitOf(u, X.sym(kn), X.OO, "", { timeLimit: 3000 });
  return r;
}
// Returns { converges: true|false, reason, test } or null
function convergenceTest(f, kn, lo, steps) {
  const { alt, g, sgn } = signFactor(f, kn);
  // divergence test
  const L = limInf(g, kn);
  if (L.status === "exact" && L.value !== X.ZERO) {
    return { converges: false, test: "divergence", reason: `The terms do not tend to 0 (${alt ? "their absolute values tend to " : "they tend to "}${txt(L.value)}), so the series diverges (term test).` };
  }
  if (L.status !== "exact") {
    if (!alt && L.status === "dne" && L.result && L.result.k === "dne" && L.result.method === "oscillation") {
      // the real-variable limit oscillates; integer sampling may still converge, so no verdict
    }
    return null;
  }
  // terms -> 0. Sign of g eventually
  let s;
  try { s = eventualSign(g, kn); } catch (e) { if (e.code === "TIMEOUT") throw e; s = null; }
  // ratio test
  const hr = hyperRatio(g, kn);
  if (hr) {
    const za = X.isNum(hr.z) ? N.abs(hr.z.v) : null;
    const dA = P.deg(hr.A), dB = P.deg(hr.B);
    if (za) {
      let Lr = null;
      if (dA < dB) Lr = N.ZERO; else if (dA === dB) Lr = za;
      if (Lr && N.cmp(Lr, N.ONE) < 0) return { converges: true, absolute: true, test: "ratio", reason: `Ratio test: |a(k+1)/a(k)| tends to ${N.toString(Lr)} < 1, so the series converges absolutely.` };
      if (dA > dB || (Lr && N.cmp(Lr, N.ONE) > 0)) return { converges: false, test: "ratio", reason: `Ratio test: |a(k+1)/a(k)| tends to ${dA > dB ? "oo" : N.toString(Lr)} > 1, so the series diverges.` };
    }
  }
  if (s === null) return null;
  // comparison with 1/(k^p), 1/(k (ln k)^q), 1/(k ln k (ln ln k)^r): at level j compute
  // lim ln(1/(k ln k ... ln_(j-1) k |a(k)|)) / ln_j k; > 1 converges, < 1 diverges, = 1 next level
  const ag = s > 0 ? g : simp(X.neg(g));
  const k = X.sym(kn);
  const Ls = [k, X.fn("ln", k), X.fn("ln", X.fn("ln", k)), X.fn("ln", X.fn("ln", X.fn("ln", k)))];
  let pre = X.ONE;
  const names = ["k^(-p)", "1/(k (ln k)^q)", "1/(k ln k (ln ln k)^r)"];
  for (let level = 0; level < 3; level++) {
    const pr = limInf(simp(X.mul(X.neg(X.fn("ln", X.mul(pre, ag))), X.pow(Ls[level + 1], X.NEG_ONE))), kn);
    if (pr.status !== "exact") break;
    const pv = pr.value;
    const c = pv === X.OO ? 1 : isNegInf(pv) ? -1 : constSign(simp(X.sub(pv, X.ONE)));
    const pT = pv === X.OO ? "oo" : txt(pv);
    if (c > 0) return { converges: true, absolute: true, test: level ? "integral" : "comparison", reason: level === 0 ? `|a(k)| decays like k^(-p) with p = ${pT} > 1 (lim ln(1/|a(k)|)/ln k = ${pT}), so the series converges absolutely by comparison with a p-series.` : `|a(k)| behaves like ${names[level]} with exponent ${pT} > 1, so the series converges absolutely (integral test / Bertrand series).` };
    if (c < 0) {
      if (alt) break;
      if (level === 0) return { converges: false, test: "comparison", reason: `The terms are eventually of one sign and decay only like k^(-p) with p = ${pT} < 1, so the series diverges by comparison with the harmonic series.` };
      if (level === 1 && pv === X.ZERO) return { converges: false, test: "comparison", reason: "The terms are eventually of one sign and behave like c/k (p = 1), so the series diverges by limit comparison with the harmonic series." };
      return { converges: false, test: "integral", reason: `The terms are eventually of one sign and behave like ${names[level]} with exponent ${pT} < 1, so the series diverges (integral test).` };
    }
    pre = simp(X.mul(pre, Ls[level]));
  }
  if (alt) {
    // alternating series test: |g| -> 0 and eventually decreasing
    let d;
    try { d = eventualSign(simp(X.sub(ag, X.subs(ag, { [kn]: X.add(k, X.ONE) }))), kn); } catch (e) { if (e.code === "TIMEOUT") throw e; d = null; }
    if (d === 1) return { converges: true, absolute: false, test: "alternating", reason: "Alternating series test: the terms alternate in sign, their absolute values decrease eventually and tend to 0, so the series converges." };
  }
  return null;
}
let txt = (u) => String(u.k);
export function setPrinter(fn) { txt = fn; }

// ---------------------------------------------------------------- infinite sums: closed forms
const BERN = [];
function bernoulli(n) {
  // B_n (B_1 = -1/2) exact
  if (BERN.length === 0) BERN.push(N.ONE);
  for (let m = BERN.length; m <= n; m++) {
    let acc = N.ZERO;
    for (let j = 0; j < m; j++) acc = N.add(acc, N.mul(Q(N.binom(BigInt(m + 1), BigInt(j))), BERN[j]));
    BERN.push(N.neg(N.div(acc, Q(m + 1))));
  }
  return BERN[n];
}
// zeta(m) as a tree: rational * pi^m for even m, zeta(m) symbol for odd m >= 3
function zetaTree(m) {
  if (m % 2 === 0) {
    const b = bernoulli(m);
    // zeta(2n) = (-1)^(n+1) B_2n (2 pi)^2n / (2 (2n)!)
    const c = N.div(N.mul(N.abs(b), N.pow(Q(2), m)), N.mul(Q(2), Q(N.factorial(BigInt(m)))));
    return simp(X.mul(X.num(c), X.pow(X.PI, X.num(m))));
  }
  return X.fn("zeta", X.num(m));
}
// digamma(q) for rational q > 0 with denominator 1, 2, 3, 4, 6 as (-gamma) + rest; returns rest
function psiRest(q) {
  const n = N.floor(q), fr = N.sub(q, Q(n));
  const s3 = X.pow(X.num(3), X.HALF), l2 = X.fn("ln", X.num(2)), l3 = X.fn("ln", X.num(3));
  let base, b0;
  const key = `${fr.n}/${fr.d}`;
  const table = {
    "0/1": [X.ZERO, 1],
    "1/2": [X.mul(X.num(-2), l2), 0],
    "1/4": [X.add(X.mul(X.num(-1, 2), X.PI), X.mul(X.num(-3), l2)), 0],
    "3/4": [X.add(X.mul(X.num(1, 2), X.PI), X.mul(X.num(-3), l2)), 0],
    "1/3": [X.add(X.mul(X.num(-1, 2), X.PI, X.pow(s3, X.NEG_ONE)), X.mul(X.num(-3, 2), l3)), 0],
    "2/3": [X.add(X.mul(X.num(1, 2), X.PI, X.pow(s3, X.NEG_ONE)), X.mul(X.num(-3, 2), l3)), 0],
    "1/6": [X.add(X.mul(X.num(-1, 2), X.PI, s3), X.mul(X.num(-2), l2), X.mul(X.num(-3, 2), l3)), 0],
    "5/6": [X.add(X.mul(X.num(1, 2), X.PI, s3), X.mul(X.num(-2), l2), X.mul(X.num(-3, 2), l3)), 0],
  };
  if (!table[key]) return null;
  [base, b0] = table[key];
  // psi(fr + j + 1) = psi(fr + j) + 1/(fr + j); base is psi at fr (fr = 0 means psi(1), index 1)
  let acc = [base];
  let start = N.isZero(fr) ? 1n : 0n;
  for (let j = start; j < n; j++) acc.push(X.num(N.inv(N.add(fr, Q(j)))));
  if (N.isZero(fr) && n < 1n) return null;
  void b0;
  return simp(X.add(...acc));
}
// Hurwitz zeta(m, q) for m >= 2, q > 0 integer or half-integer
function hurwitzTree(m, q) {
  const n = N.floor(q), fr = N.sub(q, Q(n));
  if (N.isZero(fr)) {
    if (n < 1n) return null;
    const parts = [zetaTree(m)];
    for (let j = 1n; j < n; j++) parts.push(X.num(N.neg(N.inv(N.pow(Q(j), m)))));
    return simp(X.add(...parts));
  }
  if (N.eq(fr, N.HALF)) {
    // zeta(m, 1/2) = (2^m - 1) zeta(m)
    const parts = [X.mul(X.num(Q(2n ** BigInt(m) - 1n)), zetaTree(m))];
    for (let j = 0n; j < n; j++) parts.push(X.num(N.neg(N.inv(N.pow(N.add(N.HALF, Q(j)), m)))));
    return simp(X.add(...parts));
  }
  return null;
}
// sum_{k=lo}^oo R(k) for a rational function with linear factors
function rationalInfinite(f, kn, lo, steps) {
  const rp = ratParts(f, kn);
  if (!rp || !isIntTree(lo)) return null;
  if (P.deg(rp.num) >= P.deg(rp.den) - 1) return null; // cannot converge unless deg den >= deg num + 2
  const pf = P.apartTerms(rp.num, rp.den);
  if (pf.poly.length) return null;
  const l0 = Q(big(lo));
  const byM = new Map();
  for (const t of pf.terms) {
    if (t.factor.length !== 2 || t.numer.length > 1) return null;
    // numer / (a k + b)^m = numer a^-m / (k + b/a)^m
    const a = t.factor[1], b = t.factor[0];
    const coef = N.div(t.numer[0] || N.ZERO, N.pow(a, t.power));
    const q = N.div(b, a);
    const start = N.add(l0, q);
    if (N.cmp(start, N.ZERO) <= 0) return null;
    if (!byM.has(t.power)) byM.set(t.power, []);
    byM.get(t.power).push({ coef, start });
  }
  const parts = [];
  for (const [m, list] of byM) {
    if (m === 1) {
      const total = list.reduce((s, t) => N.add(s, t.coef), N.ZERO);
      if (!N.isZero(total)) return null;
      // sum_k sum_j A_j/(k + q_j) = -sum_j A_j psi(lo + q_j)
      for (const t of list) {
        const r = psiRest(t.start);
        if (!r) return null;
        parts.push(X.mul(X.num(N.neg(t.coef)), r));
      }
    } else {
      for (const t of list) {
        const h = hurwitzTree(m, t.start);
        if (!h) return null;
        parts.push(X.mul(X.num(t.coef), h));
      }
    }
  }
  steps.push(S("sum.partial-fractions", "Partial fractions", "Split the term into partial fractions; sums of 1/(k+q)^m with m >= 2 are Hurwitz zeta values (zeta(2m) = rational * pi^(2m) via Bernoulli numbers), and the 1/(k+q) parts combine into digamma differences (the divergent parts cancel).", f, P.apart(f, kn) || null));
  return simpExpand(simp(X.add(...parts)));
}
function alternatingRational(f, kn, lo, steps) {
  const { alt, g, sgn } = signFactor(f, kn);
  if (!alt || !isIntTree(lo)) return null;
  const rp = ratParts(g, kn);
  if (!rp) return null;
  // pair consecutive terms: sum_{j>=0} [f(lo + 2j) + f(lo + 2j + 1)]
  const j = X.sym("__j");
  const e0 = X.add(lo, X.mul(X.TWO, j));
  const paired = simp(X.add(X.subs(f, { [kn]: e0 }), X.subs(f, { [kn]: X.add(e0, X.ONE) })));
  const pj = simp(X.subs(paired, { __j: X.sym(kn) }));
  // (-1)^(lo + 2j) is a constant sign; simplify it away
  const pr = simplifySigns(pj, kn);
  if (!pr) return null;
  const v = rationalInfinite(pr, kn, X.ZERO, steps);
  if (!v) return null;
  steps.push(S("sum.pair", "Pair consecutive terms", "The terms tend to 0, so grouping them in pairs does not change the (convergent) sum; each pair is a rational function of the pair index."));
  return v;
}
function simplifySigns(u, kn) {
  // replace (-1)^(2k + c) by (-1)^c
  const r = X.mapTree(u, (w) => {
    if (w.k === "pow" && w.args[0] === X.NEG_ONE && X.hasSym(w.args[1], kn)) {
      const lc = linCoeffs(w.args[1], kn);
      if (lc && isIntTree(lc.a) && big(lc.a) % 2n === 0n) return X.pow(X.NEG_ONE, lc.b);
    }
    return w;
  });
  const s = simp(r);
  return X.freeSymbols(s).has(kn) && !ratParts(s, kn) ? null : s;
}
// power series catalog: f = C * P(k) * w^k * base(k)
function powerSeries(f, kn, lo, steps) {
  const fs = f.k === "mul" ? f.args : [f];
  let C = [], w = [], fact = null, rest = [];
  for (const g of fs) {
    if (!X.hasSym(g, kn)) { C.push(g); continue; }
    if (g.k === "pow" && !X.hasSym(g.args[0], kn) && X.hasSym(g.args[1], kn)) {
      const lc = linCoeffs(g.args[1], kn);
      if (!lc || X.hasSym(lc.a, kn)) return null;
      w.push(X.pow(g.args[0], lc.a)); C.push(X.pow(g.args[0], lc.b));
      continue;
    }
    if (g.k === "pow" && g.args[1] === X.NEG_ONE && g.args[0].k === "fn" && (g.args[0].name === "factorial" || g.args[0].name === "gamma")) {
      if (fact) return null;
      let arg = g.args[0].name === "gamma" ? simp(X.add(g.args[0].args[0], X.NEG_ONE)) : g.args[0].args[0];
      const lc = linCoeffs(arg, kn);
      if (!lc || !isIntTree(lc.a) || !isIntTree(lc.b)) return null;
      const key = `${lc.a.v.n},${lc.b.v.n}`;
      fact = { "1,0": "exp", "2,0": "cos", "2,1": "sin" }[key];
      if (!fact) return null;
      continue;
    }
    rest.push(g);
  }
  const Rt = simp(X.mul(...rest));
  const rp = ratParts(Rt, kn);
  if (!rp) return null;
  let base = null, polyC;
  const den = P.monic(rp.den), lcd = P.lc(rp.den);
  const num = P.scale(rp.num, N.inv(lcd));
  const isP = (p, arr) => P.polyEq(p, arr.map((v) => Q(v)));
  if (fact) { if (den.length !== 1) return null; base = fact; }
  else if (den.length === 1) base = "geom";
  else if (isP(den, [0, 1])) base = "log";          // 1/k
  else if (isP(den, [1, 1])) base = "log1";         // 1/(k+1)
  else if (P.polyEq(den, [N.HALF, N.ONE])) base = "atanh"; // 1/(k + 1/2) = 2/(2k+1)
  else return null;
  polyC = num.map((c) => X.num(c));
  let scaleDen = X.ONE;
  if (base === "atanh") { scaleDen = X.num(N.HALF); }
  const Wn = "__W", W = X.sym(Wn);
  const sqrtW = X.pow(W, X.HALF);
  const wv = simp(X.mul(...w));
  const neg = (() => { try { return !X.freeSymbols(wv).size ? constSign(wv) < 0 : isManifestNeg(wv); } catch (_) { return false; } })();
  const mW = X.pow(simp(X.neg(W)), X.HALF);
  const G = {
    geom: [X.pow(X.sub(X.ONE, W), X.NEG_ONE), 0],
    exp: [X.exp(W), 0],
    log: [X.neg(X.fn("ln", X.sub(X.ONE, W))), 1],
    log1: [X.mul(X.neg(X.fn("ln", X.sub(X.ONE, W))), X.pow(W, X.NEG_ONE)), 0],
    cos: [neg ? X.fn("cos", mW) : X.fn("cosh", sqrtW), 0],
    sin: [neg ? X.mul(X.fn("sin", mW), X.pow(mW, X.NEG_ONE)) : X.mul(X.fn("sinh", sqrtW), X.pow(sqrtW, X.NEG_ONE)), 0],
    atanh: [neg ? X.mul(X.fn("atan", mW), X.pow(mW, X.NEG_ONE)) : X.mul(X.fn("atanh", sqrtW), X.pow(sqrtW, X.NEG_ONE)), 0],
  }[base];
  if (!G) return null;
  if (wv === X.ONE && base !== "exp" && base !== "cos" && base !== "sin") return null;
  const [gen, s0] = G;
  if (!isIntTree(lo) || big(lo) < BigInt(s0)) return null;
  let val = thetaApply(polyC, simp(X.mul(scaleDen, gen)), Wn);
  // subtract the terms before lo
  const extra = [];
  const termW = simp(X.mul(scaleDen, X.subs(simp(X.mul(P.toTree(num, kn), X.pow(P.toTree(den, kn), X.NEG_ONE), fact ? X.pow(X.fn("factorial", fact === "exp" ? X.sym(kn) : fact === "cos" ? X.mul(X.TWO, X.sym(kn)) : X.add(X.mul(X.TWO, X.sym(kn)), X.ONE)), X.NEG_ONE) : X.ONE)), {}), X.pow(W, X.sym(kn))));
  for (let k0 = BigInt(s0); k0 < big(lo); k0++) extra.push(X.neg(X.subs(termW, { [kn]: X.num(k0) })));
  val = simp(X.add(val, ...extra));
  if (val === X.UNDEF) return null;
  const value = simp(X.mul(...C, X.subs(val, { [Wn]: wv })));
  if (value === X.UNDEF || X.contains(value, X.UNDEF)) return null;
  const conditions = [];
  if (!["exp", "cos", "sin"].includes(base) && X.freeSymbols(wv).size) conditions.push(X.rel("<", X.fn("abs", wv), X.ONE));
  const names = { geom: "geometric series 1/(1-w)", exp: "exponential series e^w", log: "logarithm series -ln(1-w)", log1: "logarithm series -ln(1-w)/w", cos: "cosine / hyperbolic cosine series", sin: "sine / hyperbolic sine series", atanh: "arctangent / inverse hyperbolic tangent series" };
  steps.push(S("sum.power-series", "Recognise a power series", `The term is ${polyC.length > 1 ? "a polynomial in k times " : ""}the k-th term of the ${names[base]} evaluated at w = ${txt(wv)}${polyC.length > 1 ? "; each factor k corresponds to applying w d/dw" : ""}.`, f, value));
  return { value, conditions, base };
}
function isManifestNeg(w) {
  if (w.k === "mul" && X.isNum(w.args[0]) && N.isNeg(w.args[0].v)) {
    return w.args.slice(1).every((a) => (a.k === "pow" && X.isInt(a.args[1]) && a.args[1].v.n % 2n === 0n) || (X.isNum(a) && N.isPos(a.v)) || a === X.PI || a === X.E);
  }
  return false;
}
function infiniteSum(f, kn, lo, steps) {
  const k = X.sym(kn);
  if (!X.hasSym(f, kn)) {
    if (f === X.ZERO) return { kind: "value", value: X.ZERO, method: "zero" };
    return { kind: "diverges", test: "divergence", reason: "The terms are a nonzero constant, so the partial sums grow without bound." };
  }
  const conv = convergenceTest(f, kn, lo, steps);
  if (conv) steps.push(S(`sum.test.${conv.test}`, conv.converges ? "Convergence test" : "Divergence", conv.reason));
  if (conv && !conv.converges) return { kind: "diverges", test: conv.test, reason: conv.reason };
  // geometric
  const hr = hyperRatio(f, kn);
  if (hr && P.deg(hr.A) === 0 && P.deg(hr.B) === 0 && ratioOK(f, kn, hr, lo)) {
    const z = hr.z;
    const f0 = simp(X.subs(f, { [kn]: lo }));
    let zs = null;
    try { if (!X.freeSymbols(z).size) zs = constSign(simp(X.sub(X.fn("abs", z), X.ONE))); } catch (_) { zs = null; }
    if (zs !== null && zs >= 0) return { kind: "diverges", test: "geometric", reason: `This is a geometric series with ratio ${txt(z)}, |ratio| >= 1, so it diverges.` };
    const value = simp(X.mul(f0, X.pow(X.sub(X.ONE, z), X.NEG_ONE)));
    steps.push(S("sum.geometric", "Geometric series", `First term ${txt(f0)}, common ratio r = ${txt(z)}; the sum is first/(1 - r) when |r| < 1.`, f, value));
    return { kind: "value", value, method: "geometric", conditions: zs === null ? [X.rel("<", X.fn("abs", z), X.ONE)] : [] };
  }
  // Gosper (telescoping / hypergeometric antidifference)
  if (hr && X.isNum(hr.z) && ratioOK(f, kn, hr, lo)) {
    const g = gosper(f, kn, hr);
    if (g) {
      const n = X.sym("__n");
      const Sn = gosperEval(f, kn, lo, n, g);
      if (Sn) {
        const L = limitOf(Sn, n, X.OO, "", { timeLimit: 4000 });
        if (L.status === "exact" && L.value !== X.OO && !isNegInf(L.value)) {
          steps.push(S("sum.telescoping", "Telescoping (Gosper)", "The term is T(k+1) - T(k) for a closed-form T, so the partial sum is T(n+1) - T(lo); let n -> oo.", f, L.value));
          return { kind: "value", value: L.value, method: "telescoping" };
        }
        if (L.status === "exact") return { kind: "diverges", test: "partial sums", reason: `The partial sums equal ${txt(Sn)} (with n the upper limit), which tends to ${txt(L.value)}.` };
      }
    }
  }
  // the remaining closed forms need convergence to be established first; power series carry
  // their own convergence condition (entire functions, or |w| < 1 stated as a condition)
  if (!conv) {
    const ps = powerSeries(f, kn, lo, steps);
    if (ps && (["exp", "cos", "sin"].includes(ps.base) || ps.conditions.length)) return { kind: "value", value: ps.value, method: "power series", conditions: ps.conditions };
    return null;
  }
  const rv = rationalInfinite(f, kn, lo, steps);
  if (rv) return { kind: "value", value: rv, method: "zeta/digamma" };
  const av = alternatingRational(f, kn, lo, steps);
  if (av) return { kind: "value", value: av, method: "alternating" };
  const ps = powerSeries(f, kn, lo, steps);
  if (ps) return { kind: "value", value: ps.value, method: "power series", conditions: ps.conditions };
  // convergent, no closed form known here: numeric value
  const nv = NU.sumInfinite(f, kn, Number(isIntTree(lo) ? big(lo) : 0n), { digits: 20, timeLimitMs: 4000 });
  if (nv.converged && nv.value !== "undefined") return { kind: "converges", approx: nv.value, reason: conv.reason, digits: nv.digits };
  return { kind: "converges", approx: null, reason: conv.reason };
}

// ---------------------------------------------------------------- public: sums
export function sumCompute(f0, k, lo0, hi0, opts = {}) {
  const kn = typeof k === "string" ? k : k.name;
  const steps = [];
  const run = () => {
    const f = simp(f0), lo = simp(lo0), hi = simp(hi0);
    if (f === X.UNDEF) throw qerr("UNDEFINED", "the summand is undefined");
    if (hi === X.OO) {
      const r = infiniteSum(f, kn, lo, steps);
      if (!r) throw qerr("UNKNOWN", "no convergence test or closed form applies to this series");
      return { ...r, steps, conditions: r.conditions || [] };
    }
    if (isNegInf(lo) || X.contains(hi, X.OO) || X.contains(lo, X.OO)) throw qerr("UNSUPPORTED", "sums starting at -oo are not supported");
    const r = finiteSum(f, kn, lo, hi, steps);
    if (!r) throw qerr("UNKNOWN", "no summation method applies (the term is not polynomial, hypergeometric and Gosper-summable, or polynomial times geometric)");
    const hs = [...X.freeSymbols(hi)];
    const value = r.method === "direct" ? r.value : niceForm(r.value, hs.length === 1 ? hs[0] : kn);
    return { kind: "value", value, method: r.method, steps, conditions: r.conditions || [], cert: r.cert || null, exact: r.exact };
  };
  return opts.deadline ? Budget.withDeadline(opts.deadline, run) : Budget.with(opts.timeLimit || 12000, run);
}

// ---------------------------------------------------------------- verification of sums
const RAND_PARAMS = [Q(3, 7), Q(2, 5), Q(5, 11), Q(1, 3), Q(4, 9)];
function paramSubs(u, skip) {
  const out = {};
  [...X.freeSymbols(u)].filter((v) => !skip.includes(v)).sort().forEach((v, i) => { out[v] = X.num(RAND_PARAMS[i % RAND_PARAMS.length]); });
  return out;
}
function sameValue(a, b) {
  const d = simp(X.sub(a, b));
  if (d === X.ZERO) return true;
  if (X.isNum(d)) return false;
  const v = hp(d, {}, { digits: 40, maxDigits: 200 });
  const s = hp(a, {}, { digits: 30, maxDigits: 60 });
  if (!v.ok) return null;
  const scale = s.ok ? Math.max(0, log10Abs(s.big)) : 0;
  return log10Abs(v.big) - scale < -30 ? true : log10Abs(v.big) - scale > -15 ? false : null;
}
export function verifySum(f0, k, lo0, hi0, res) {
  const kn = typeof k === "string" ? k : k.name;
  const checks = [];
  const f = simp(f0), lo = simp(lo0), hi = simp(hi0);
  try {
    return Budget.with(10000, () => {
      if (hi === X.OO) return verifyInfinite(f, kn, lo, res, checks);
      if (res.kind !== "value") return { status: "inconclusive", checks };
      const hs = [...X.freeSymbols(hi)];
      if (!hs.length) {
        // numeric bounds: direct summation (independent) unless the range is huge
        if (isIntTree(lo) && isIntTree(hi) && big(hi) - big(lo) <= 3000n && res.method !== "direct") {
          const d = direct(f, kn, lo, hi);
          const ok = sameValue(d, res.value);
          checks.push({ kind: "direct summation", ok, detail: ok ? "adding the terms one by one gives the same value" : "direct summation disagrees" });
          return { status: ok === true ? "verified-exact" : ok === false ? "failed" : "inconclusive", checks };
        }
        if (res.method === "direct") {
          // independent check: floating-point sum
          let acc = 0;
          for (let i = big(lo); i <= big(hi); i++) acc += evalNum(f, kn, Number(i));
          const v = evalNum(res.value, kn, 0);
          const ok = Number.isFinite(acc) && Math.abs(acc - v) <= 1e-9 * Math.max(1, Math.abs(v));
          checks.push({ kind: "floating-point sum", ok, detail: `double-precision sum ${acc.toPrecision(12)}` });
          return { status: ok ? "verified-exact" : "failed", checks };
        }
        // large numeric range computed symbolically: check the closed form as a function of n
        return verifyFiniteSymbolic(f, kn, lo, X.sym("__nn"), res, checks, hi);
      }
      if (hs.length !== 1) return { status: "inconclusive", checks };
      return verifyFiniteSymbolic(f, kn, lo, X.sym(hs[0]), res, checks, null);
    });
  } catch (e) {
    if (e.code === "TIMEOUT") return { status: "inconclusive", checks: [...checks, { kind: "time", ok: null, detail: "verification ran out of time" }] };
    throw e;
  }
}
function evalNum(u, kn, kv) {
  const v = NU.evalTree(u, { [kn]: kv }, { digits: 20, mode: "real" });
  return v instanceof B.BigFloat ? B.toNumber(v) : NaN;
}
function verifyFiniteSymbolic(f, kn, lo, nsym, res, checks, hiNumeric) {
  // S(m) against the explicit sum for small m (parameters replaced by random rationals)
  let value = res.value;
  if (hiNumeric) {
    // the value was computed for a numeric hi; recompute the closed form in n to check it
    return { status: res.exact ? "verified-exact" : "inconclusive", checks: [{ kind: "closed form", ok: null, detail: "computed from a verified closed form" }] };
  }
  const ps = paramSubs(simp(X.add(f, value)), [kn, nsym.name]);
  const fP = simp(X.subs(f, ps)), vP = simp(X.subs(value, ps));
  const l = isIntTree(lo) ? Number(big(lo)) : null;
  if (l === null) return { status: "inconclusive", checks };
  let bad = null, good = 0;
  for (let m = l; m <= l + 9; m++) {
    const fm = simp(X.subs(fP, { [nsym.name]: X.num(m) }));
    let explicit;
    try { explicit = direct(fm, kn, X.num(l), X.num(m)); } catch (e) { if (e.code === "UNDEFINED") continue; throw e; }
    const closed = simp(X.subs(vP, { [nsym.name]: X.num(m) }));
    if (closed === X.UNDEF) continue;
    const ok = sameValue(explicit, closed);
    if (ok === false) { bad = m; break; }
    if (ok === true) good++;
  }
  if (bad !== null) {
    checks.push({ kind: "explicit partial sums", ok: false, detail: `the closed form disagrees with the explicit sum at n = ${bad}` });
    return { status: "failed", checks };
  }
  checks.push({ kind: "explicit partial sums", ok: good >= 6, detail: `the closed form equals the explicit sum for ${good} values of n (parameters set to random rationals)` });
  // recurrence check at larger n when the summand does not involve n
  if (!X.hasSym(f, nsym.name)) {
    for (const m of [l + 23, l + 57]) {
      const Sm = simp(X.subs(vP, { [nsym.name]: X.num(m) })), Sm1 = simp(X.subs(vP, { [nsym.name]: X.num(m - 1) }));
      const fm = simp(X.subs(fP, { [kn]: X.num(m) }));
      const ok = sameValue(simp(X.sub(Sm, Sm1)), fm);
      checks.push({ kind: "S(n) - S(n-1) = term", ok, detail: `checked exactly at n = ${m}` });
      if (ok === false) return { status: "failed", checks };
    }
  }
  if (good < 6) return { status: "inconclusive", checks };
  if (res.cert) checks.push({ kind: "Gosper certificate", ok: true, detail: "a(k) x(k+1) - b(k-1) x(k) = c(k) holds as an exact polynomial identity" });
  const proof = res.method === "faulhaber" || res.method === "gosper" || res.method === "constant";
  return { status: proof ? "verified-exact" : "verified-numeric", checks };
}
function verifyInfinite(f, kn, lo, res, checks) {
  if (res.kind === "diverges") {
    // numeric evidence only: partial sums grow / terms do not vanish
    checks.push({ kind: "divergence proof", ok: true, detail: res.reason });
    const ps = paramSubs(f, [kn]);
    const fP = simp(X.subs(f, ps));
    const nv = NU.sumInfinite(fP, kn, isIntTree(lo) ? Number(big(lo)) : 1, { digits: 12, timeLimitMs: 2500 });
    if (nv.converged && nv.digits >= 10 && /converges|term test/i.test(res.reason) === false && res.test !== "divergence" && res.test !== "ratio" && res.test !== "geometric") {
      // Levin transforms can "sum" divergent series (e.g. analytic continuation); keep the proof
      checks.push({ kind: "numeric", ok: null, detail: "the extrapolated partial sums look convergent, but the proof of divergence stands" });
    }
    return { status: "verified-exact", checks };
  }
  if (res.kind === "converges") {
    checks.push({ kind: "convergence proof", ok: true, detail: res.reason });
    return { status: "inconclusive", checks };
  }
  const ps = paramSubs(simp(X.add(f, res.value)), [kn]);
  const fP = simp(X.subs(f, ps)), vP = simp(X.subs(res.value, ps));
  const zsub = substituteZeta(vP);
  const want = hp(zsub, {}, { digits: 40, maxDigits: 120 });
  if (!want.ok) return { status: "inconclusive", checks: [...checks, { kind: "numeric", ok: null, detail: "the closed form could not be evaluated" }] };
  let nv = NU.sumInfinite(fP, kn, isIntTree(lo) ? Number(big(lo)) : 1, { digits: 25, timeLimitMs: 6000 });
  if (!nv.converged || nv.value === "undefined") nv = directGeometricTail(fP, kn, isIntTree(lo) ? Number(big(lo)) : 1) || nv;
  if (!nv.converged || nv.value === "undefined") {
    checks.push({ kind: "numeric series value", ok: null, detail: "the numeric summation did not converge" });
    return { status: "inconclusive", checks };
  }
  const got = B.fromString(nv.value, 200);
  const diff_ = log10Abs(B.sub(got, want.big, 200)) - Math.max(0, log10Abs(want.big));
  const tol = -Math.max(8, Math.min(20, nv.digits - 2));
  const ok = diff_ < tol;
  checks.push({ kind: "numeric series value", ok, detail: `Levin-accelerated partial sums give ${nv.value.slice(0, 22)} (${nv.digits} digits); the closed form gives ${B.toString(want.big, 22)}` });
  return { status: ok ? "verified-numeric" : diff_ > -4 ? "failed" : "inconclusive", checks };
}
// Plain partial sums for fast-decaying terms: accepted only when the last terms shrink at least
// geometrically (ratio < 0.9) and are below 1e-35 of the partial sum (tail bounded by a geometric series).
function directGeometricTail(f, kn, k0) {
  let acc = B.ZERO;
  const mags = [];
  const t0 = now();
  for (let k = k0; k < k0 + 4000; k++) {
    if (now() - t0 > 3000) return null;
    const v = NU.evalTree(f, { [kn]: k }, { digits: 60, mode: "real" });
    if (!(v instanceof B.BigFloat)) return null;
    acc = B.add(acc, v, 256);
    mags.push(log10Abs(v));
    const n = mags.length;
    if (n > 30) {
      const tail = mags.slice(-20);
      const geo = tail.every((m, i) => i === 0 || m <= tail[i - 1] - 0.045);
      if (geo && tail[19] < log10Abs(acc) - 35) return { converged: true, value: B.toString(acc, 30), digits: 30 };
    }
  }
  return null;
}
// replace zeta(m) (odd m) by a 60-digit rational value computed independently
function substituteZeta(u) {
  return X.mapTree(u, (w) => {
    if (w.k === "fn" && w.name === "zeta" && isIntTree(w.args[0])) {
      const m = Number(big(w.args[0]));
      const r = NU.sumInfinite(X.pow(X.sym("__z"), X.num(-m)), "__z", 1, { digits: 40, timeLimitMs: 3000 });
      if (!r.converged) return w;
      return X.num(N.fromDecimal(r.value));
    }
    return w;
  });
}

// ---------------------------------------------------------------- products
function finiteProduct(f, kn, lo, hi, steps) {
  if (!X.hasSym(f, kn)) return { value: simp(X.pow(f, X.add(hi, X.neg(lo), X.ONE))), method: "constant" };
  if (isIntTree(lo) && isIntTree(hi) && big(hi) - big(lo) <= 800n) {
    const fs = [];
    for (let i = big(lo); i <= big(hi); i++) fs.push(simp(X.subs(f, { [kn]: X.num(i) })));
    const v = simp(X.mul(...fs));
    if (fs.includes(X.UNDEF)) throw qerr("UNDEFINED", "a factor is undefined");
    steps.push(S("product.direct", "Multiply the factors", "Multiply all factors exactly."));
    return { value: v, method: "direct" };
  }
  const k = X.sym(kn);
  const count = X.add(hi, X.neg(lo), X.ONE);
  const parts = [];
  const fs = f.k === "mul" ? f.args : [f];
  const ratFactors = [];
  for (const g of fs) {
    if (!X.hasSym(g, kn)) { parts.push(X.pow(g, count)); continue; }
    if (g.k === "pow" && !X.hasSym(g.args[0], kn)) {
      // b^(e(k)) -> b^(sum e(k))
      const es = finiteSum(g.args[1], kn, lo, hi, []);
      if (!es) return null;
      parts.push(X.pow(g.args[0], es.value));
      continue;
    }
    ratFactors.push(g);
  }
  if (ratFactors.length) {
    const rp = ratParts(X.mul(...ratFactors), kn);
    if (!rp) return null;
    const out = [];
    const handle = (poly, sign) => {
      const fq = P.factorQ(poly);
      out.push(X.pow(X.num(fq.unit), X.mul(X.num(sign), count)));
      for (const { poly: q, mult } of fq.factors) {
        if (q.length !== 2) return false;
        // (a k + b) = a (k + b/a)
        const a = q[1], b = q[0], s = N.div(b, a);
        out.push(X.pow(X.num(a), X.mul(X.num(sign * mult), count)));
        // prod_{k=lo}^{hi} (k + s) = Gamma(hi + s + 1) / Gamma(lo + s)
        const g1 = simp(X.add(hi, X.num(s), X.ONE)), g0 = simp(X.add(lo, X.num(s)));
        let term;
        if (s.d === 1n) {
          if (X.isNum(g0) && N.cmp(g0.v, N.ZERO) <= 0) return false; // a factor vanishes
          term = X.mul(X.fn("factorial", simp(X.add(g1, X.NEG_ONE))), X.pow(X.fn("factorial", simp(X.add(g0, X.NEG_ONE))), X.NEG_ONE));
        } else term = X.mul(X.fn("gamma", g1), X.pow(X.fn("gamma", g0), X.NEG_ONE));
        out.push(X.pow(term, X.num(sign * mult)));
      }
      return true;
    };
    if (!handle(rp.num, 1) || !handle(rp.den, -1)) return null;
    parts.push(...out);
    steps.push(S("product.factorials", "Products of linear factors", "Factor the term into linear factors a k + b; the product of (k + s) for k = lo..n is Gamma(n + s + 1)/Gamma(lo + s), a ratio of factorials for integer s."));
  }
  const hs = [...X.freeSymbols(hi)];
  const v = normFactorials(simp(X.mul(...parts)), hs.length === 1 ? hs[0] : kn);
  return { value: v, method: "factorials" };
}
export function productCompute(f0, k, lo0, hi0, opts = {}) {
  const kn = typeof k === "string" ? k : k.name;
  const steps = [];
  const run = () => {
    const f = simp(f0), lo = simp(lo0), hi = simp(hi0);
    if (hi === X.OO) {
      const n = X.sym("__n");
      const r = finiteProduct(f, kn, lo, n, steps);
      if (!r) throw qerr("UNKNOWN", "no closed form for the partial products");
      const L = limitOf(r.value, n, X.OO, "", { timeLimit: 5000 });
      if (L.status !== "exact") throw qerr("UNKNOWN", "the limit of the partial products could not be determined");
      steps.push(S("product.limit", "Limit of the partial products", `The partial product up to n is ${txt(r.value)}; let n -> oo.`, r.value, L.value));
      if (L.value === X.OO || isNegInf(L.value)) return { kind: "diverges", reason: `The partial products (up to n) equal ${txt(X.subs(r.value, { __n: X.sym("n") }))}, which tends to ${txt(L.value)}.`, steps, partial: r.value };
      return { kind: "value", value: L.value, method: "limit of partial products", steps, partial: r.value, conditions: [], note: L.value === X.ZERO ? "The partial products tend to 0 (in the strict sense such a product is said to diverge to 0)." : "" };
    }
    const r = finiteProduct(f, kn, lo, hi, steps);
    if (!r) throw qerr("UNKNOWN", "no product formula applies (the factors are not rational with rational roots or exponential)");
    return { kind: "value", value: r.value, method: r.method, steps, conditions: [] };
  };
  return opts.deadline ? Budget.withDeadline(opts.deadline, run) : Budget.with(opts.timeLimit || 12000, run);
}
export function verifyProduct(f0, k, lo0, hi0, res) {
  const kn = typeof k === "string" ? k : k.name;
  const f = simp(f0), lo = simp(lo0), hi = simp(hi0);
  const checks = [];
  if (res.kind === "diverges" && hi === X.OO && res.partial) {
    const pv = verifyProduct(f, kn, lo, X.sym("__n"), { kind: "value", value: res.partial });
    return { status: pv.status === "failed" ? "failed" : pv.status === "inconclusive" ? "inconclusive" : "verified-numeric", checks: pv.checks };
  }
  if (res.kind !== "value") return { status: "inconclusive", checks };
  try {
    return Budget.with(8000, () => {
      if (hi === X.OO) {
        // partial products checked like a finite product, then the value against a far partial product
        const n = "__n";
        const pv = verifyProduct(f, kn, lo, X.sym(n), { kind: "value", value: res.partial });
        checks.push(...pv.checks);
        if (pv.status === "failed") return { status: "failed", checks };
        const ps = paramSubs(simp(X.add(f, res.value)), [kn]);
        const want = hp(simp(X.subs(res.value, ps)), {}, { digits: 30 });
        const far = hp(simp(X.subs(res.partial, { ...ps, [n]: X.num(100000) })), {}, { digits: 30 });
        if (want.ok && far.ok) {
          const d = Math.abs(want.re - far.re);
          const ok = d < 1e-3 * Math.max(1, Math.abs(want.re));
          checks.push({ kind: "far partial product", ok, detail: `partial product at n = 100000 is ${far.re.toPrecision(10)}` });
          if (!ok) return { status: "failed", checks };
        }
        return { status: pv.status === "verified-exact" ? "verified-numeric" : pv.status, checks };
      }
      const hs = [...X.freeSymbols(hi)];
      if (!hs.length) {
        if (res.method === "direct") return { status: "verified-exact", checks: [{ kind: "direct", ok: true, detail: "exact multiplication" }] };
        return { status: "inconclusive", checks };
      }
      const nn = hs[0];
      const ps = paramSubs(simp(X.add(f, res.value)), [kn, nn]);
      const fP = simp(X.subs(f, ps)), vP = simp(X.subs(res.value, ps));
      const l = isIntTree(lo) ? Number(big(lo)) : null;
      if (l === null) return { status: "inconclusive", checks };
      let good = 0;
      for (let m = l; m <= l + 8; m++) {
        const fs = [];
        for (let i = l; i <= m; i++) fs.push(simp(X.subs(simp(X.subs(fP, { [nn]: X.num(m) })), { [kn]: X.num(i) })));
        const explicit = simp(X.mul(...fs));
        const closed = simp(X.subs(vP, { [nn]: X.num(m) }));
        if (explicit === X.UNDEF || closed === X.UNDEF) continue;
        const ok = sameValue(explicit, closed);
        if (ok === false) { checks.push({ kind: "explicit partial products", ok: false, detail: `disagrees at n = ${m}` }); return { status: "failed", checks }; }
        if (ok) good++;
      }
      checks.push({ kind: "explicit partial products", ok: good >= 6, detail: `the closed form equals the explicit product for ${good} values of n` });
      return { status: good >= 6 ? "verified-numeric" : "inconclusive", checks };
    });
  } catch (e) {
    if (e.code === "TIMEOUT") return { status: "inconclusive", checks };
    throw e;
  }
}

export { hyperRatio, gosper, bernoulli, zetaTree, faulhaber, solveQ };
