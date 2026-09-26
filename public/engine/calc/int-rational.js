// Quelvra integration of rational functions over Q (real results only).
//
//   polynomial part     : term-wise
//   rational part       : Hermite reduction (Mack's linear version, Bronstein alg. 2.2)
//   logarithmic part    : squarefree denominator D, factored over Q; for each irreducible factor f
//        deg 1          : c ln|f|
//        deg 2          : (B/2) ln(q) + (2C - B s)/sqrt(4p - s^2) atan((2x + s)/sqrt(4p - s^2))
//                         or the ln|(2x+s-sqrt(D))/(2x+s+sqrt(D))| form when the roots are real
//        deg >= 3       : Rothstein-Trager resultant R(t) = res_x(f, A - t f'); when R splits over Q
//                         the result is sum c ln|gcd(f, A - c f')| (Lazard-Rioboo-Trager style).
//                         Otherwise f is split over a real algebraic field K = Q(alpha) with exact
//                         arithmetic (alpha = sqrt(k) found for quartics, or a real closed-form root
//                         of f for cubics), and partial fractions are taken over K: every coefficient
//                         is exact, only real logs and arctangents appear (no complex numbers).
// Every splitting over K is verified by exact multiplication before it is used.

import * as X from "../expr.js";
import * as N from "../num.js";
import * as C from "../poly.js";
import { canon, evalD } from "./int-util.js";

const Q0 = N.ZERO, Q1 = N.ONE;
const unsupported = (m) => Object.assign(new Error(m), { code: "UNSUPPORTED" });

// ---------------------------------------------------------------- algebraic field K = Q[t]/(m)
class Field {
  constructor(m, alpha, alphaVal) { this.m = C.monic(m); this.n = this.m.length - 1; this.alpha = alpha; this.val = alphaVal; }
  static Q() { return new Field([Q0, Q1], X.ZERO, 0); }
  isQ() { return this.n === 1 && this.m[0].n === 0n; }
  red(a) { a = C.norm(a); return a.length > this.n ? C.rem(a, this.m) : a; }
  add(a, b) { return C.add(a, b); }
  sub(a, b) { return C.sub(a, b); }
  neg(a) { return C.neg(a); }
  mul(a, b) { return this.red(C.mul(a, b)); }
  inv(a) {
    if (!a.length) throw new RangeError("division by zero in field");
    if (a.length === 1) return [N.inv(a[0])];
    const { g, s } = C.xgcd(a, this.m);
    if (g.length !== 1) throw new Error("Quelvra: field modulus is not irreducible");
    return this.red(C.scale(s, N.inv(g[0])));
  }
  div(a, b) { return this.mul(a, this.inv(b)); }
  q(r) { return C.norm([typeof r === "object" ? r : N.Q(r)]); }
  zero(a) { return a.length === 0; }
  value(a) { let s = 0; for (let i = a.length - 1; i >= 0; i--) s = s * this.val + N.toFloat(a[i]); return s; }
  tree(a) {
    if (!a.length) return X.ZERO;
    const terms = a.map((c, i) => (c.n === 0n ? null : (i === 0 ? X.num(c) : X.mul(X.num(c), X.pow(this.alpha, X.num(i)))))).filter(Boolean);
    return canon(X.add(...terms));
  }
}

// ---------------------------------------------------------------- polynomials over K (arrays of elements)
const pn = (p) => { let n = p.length; while (n > 0 && p[n - 1].length === 0) n--; return n === p.length ? p : p.slice(0, n); };
const padd = (K, a, b) => { const n = Math.max(a.length, b.length), o = []; for (let i = 0; i < n; i++) o.push(K.add(a[i] || [], b[i] || [])); return pn(o); };
const psub = (K, a, b) => { const n = Math.max(a.length, b.length), o = []; for (let i = 0; i < n; i++) o.push(K.sub(a[i] || [], b[i] || [])); return pn(o); };
function pmul(K, a, b) {
  if (!a.length || !b.length) return [];
  const o = Array.from({ length: a.length + b.length - 1 }, () => []);
  for (let i = 0; i < a.length; i++) { if (!a[i].length) continue; for (let j = 0; j < b.length; j++) o[i + j] = K.add(o[i + j], K.mul(a[i], b[j])); }
  return pn(o);
}
const pscale = (K, p, c) => pn(p.map((e) => K.mul(e, c)));
function pdivmod(K, a, b) {
  b = pn(b); a = pn(a);
  if (!b.length) throw new RangeError("division by zero polynomial");
  const db = b.length - 1;
  if (a.length - 1 < db) return { q: [], r: a };
  const r = a.slice(), q = Array.from({ length: a.length - db }, () => []);
  const inv = K.inv(b[db]);
  for (let i = a.length - 1; i >= db; i--) {
    if (!r[i].length) continue;
    const t = K.mul(r[i], inv);
    q[i - db] = t;
    for (let j = 0; j <= db; j++) r[i - db + j] = K.sub(r[i - db + j], K.mul(t, b[j]));
  }
  return { q: pn(q), r: pn(r.slice(0, db)) };
}
const pderiv = (K, p) => pn(p.slice(1).map((c, i) => K.mul(c, K.q(i + 1))));
const pmonic = (K, p) => (p.length ? pscale(K, p, K.inv(p[p.length - 1])) : p);
function pgcd(K, a, b) {
  a = pn(a); b = pn(b);
  let guard = a.length + b.length + 4;
  while (b.length) { if (--guard < 0) throw unsupported("gcd did not terminate"); const r = pdivmod(K, a, b).r; a = b; b = r; }
  return pmonic(K, a);
}
function pxgcd(K, a, b) {
  let r0 = pn(a), r1 = pn(b), s0 = [K.q(1)], s1 = [], t0 = [], t1 = [K.q(1)];
  let guard = r0.length + r1.length + 4;
  while (r1.length) {
    if (--guard < 0) throw unsupported("xgcd did not terminate");
    const { q, r } = pdivmod(K, r0, r1);
    [r0, r1] = [r1, r];
    [s0, s1] = [s1, psub(K, s0, pmul(K, q, s1))];
    [t0, t1] = [t1, psub(K, t0, pmul(K, q, t1))];
  }
  const k = K.inv(r0[r0.length - 1]);
  return { g: pscale(K, r0, k), s: pscale(K, s0, k), t: pscale(K, t0, k) };
}
const fromQpoly = (K, p) => pn(p.map((c) => K.q(c)));
function ptree(K, p, x) {
  const terms = [];
  p.forEach((c, i) => { if (c.length) terms.push(X.mul(K.tree(c), X.pow(x, X.num(i)))); });
  return canon(X.add(...terms));
}
const peval = (K, p, e) => { let acc = []; for (let i = p.length - 1; i >= 0; i--) acc = K.add(K.mul(acc, e), p[i]); return acc; };

// ---------------------------------------------------------------- helpers over Q
const qtree = (p, x) => C.toTree(p, x.name);
// s*a + t*b = c with deg s < deg b (gcd(a, b) = 1)
function extEuclid(a, b, c) {
  const { g, s: s0 } = C.xgcd(a, b);
  if (g.length !== 1) throw new Error("Quelvra: internal error (Hermite reduction: gcd != 1)");
  const s = C.rem(C.mul(s0, c), b);
  const t = C.exactDiv(C.sub(c, C.mul(s, a)), b);
  if (t === null) throw new Error("Quelvra: internal error (extended Euclid)");
  return { s, t };
}

// Hermite reduction: A/D (deg A < deg D) = (g)' + A*/D* with D* squarefree.
export function hermite(A, D) {
  const parts = [];
  let Dm = C.gcd(D, C.deriv(D));
  const Ds = C.exactDiv(D, Dm);
  let guard = D.length + 2;
  while (Dm.length > 1) {
    if (--guard < 0) throw unsupported("Hermite reduction did not terminate");
    const Dm2 = C.gcd(Dm, C.deriv(Dm));
    const Dms = C.exactDiv(Dm, Dm2);
    // (B, Cc) with B*(-Ds*Dm'/Dm) + Cc*Dms = A
    const a = C.neg(C.exactDiv(C.mul(Ds, C.deriv(Dm)), Dm));
    const { s: Bp, t: Cp } = extEuclid(a, Dms, A);
    A = C.sub(Cp, C.exactDiv(C.mul(C.deriv(Bp), Ds), Dms));
    if (Bp.length) parts.push({ num: Bp, den: Dm });
    Dm = Dm2;
  }
  return { parts, A, D: Ds };
}

// numeric recognition of a rational (continued fractions), verified by the caller
export function recognizeRational(v, maxDen = 100000) {
  if (!Number.isFinite(v)) return null;
  const sgn = v < 0 ? -1n : 1n;
  let x = Math.abs(v);
  let h0 = 0n, h1 = 1n, k0 = 1n, k1 = 0n;
  for (let i = 0; i < 40; i++) {
    const a = Math.floor(x);
    if (a > 1e15) break;
    const A = BigInt(a);
    [h0, h1] = [h1, A * h1 + h0];
    [k0, k1] = [k1, A * k1 + k0];
    if (k1 > BigInt(maxDen)) return null;
    const approx = Number(h1) / Number(k1);
    if (Math.abs(approx - Math.abs(v)) <= 1e-9 * Math.max(1, Math.abs(v))) return N.Q(sgn * h1, k1);
    const fr = x - a;
    if (fr < 1e-15) break;
    x = 1 / fr;
  }
  return null;
}
function squarefreeInt(n) {
  // n = s^2 * k with k squarefree (n > 0 small)
  const { factors, rest } = N.trialFactor(n);
  if (rest !== 1n) return null;
  let k = 1n, s = 1n;
  for (const [p, e] of factors) { if (e % 2n === 1n) k *= p; s *= p ** (e / 2n); }
  return { k, s };
}

// Try to split a monic quartic f over Q(sqrt(k)) into two real quadratics.
function splitQuarticSqrt(f) {
  const roots = C.complexRoots(f);
  if (roots.length !== 4) return null;
  const pairings = [[[0, 1], [2, 3]], [[0, 2], [1, 3]], [[0, 3], [1, 2]]];
  for (const [[i, j], [k2, l]] of pairings) {
    const sp = (a, b) => ({ s: { re: roots[a].re + roots[b].re, im: roots[a].im + roots[b].im }, p: { re: roots[a].re * roots[b].re - roots[a].im * roots[b].im, im: roots[a].re * roots[b].im + roots[a].im * roots[b].re } });
    const A1 = sp(i, j), A2 = sp(k2, l);
    if ([A1.s.im, A1.p.im, A2.s.im, A2.p.im].some((v) => Math.abs(v) > 1e-9)) continue;
    const s1 = A1.s.re, s2 = A2.s.re, p1 = A1.p.re, p2 = A2.p.re;
    const sa = recognizeRational((s1 + s2) / 2), pa = recognizeRational((p1 + p2) / 2);
    const sd = recognizeRational(((s1 - s2) / 2) ** 2), pd = recognizeRational(((p1 - p2) / 2) ** 2);
    if (!sa || !pa || !sd || !pd || N.isNeg(sd) || N.isNeg(pd)) continue;
    // common k: sd = bs^2 k, pd = bp^2 k
    const ref = !N.isZero(sd) ? sd : pd;
    if (N.isZero(ref)) continue;
    const num = ref.n * ref.d; // ref = num / d^2
    const sq = squarefreeInt(num);
    if (!sq || sq.k === 1n) continue;
    const k = sq.k;
    const coef = (d, approxSign) => {
      if (N.isZero(d)) return Q0;
      const r = N.div(d, N.Q(k)); // b^2
      if (N.isNeg(r)) return null;
      const [bn, e1] = N.iroot(r.n, 2), [bd, e2] = N.iroot(r.d, 2);
      if (!e1 || !e2) return null;
      return N.Q(approxSign < 0 ? -bn : bn, bd);
    };
    const bs = coef(sd, s1 - s2), bp = coef(pd, p1 - p2);
    if (bs === null || bp === null) continue;
    const K = new Field([N.Q(-k), Q0, Q1], X.sqrt(X.num(k)), Math.sqrt(Number(k)));
    // quadratics x^2 - s x + p with s = sa +- bs sqrt k, p = pa +- bp sqrt k
    const q1 = [C.norm([pa, bp]), C.norm([N.neg(sa), N.neg(bs)]), [Q1]];
    const q2 = [C.norm([pa, N.neg(bp)]), C.norm([N.neg(sa), bs]), [Q1]];
    const prod = pmul(K, q1, q2);
    const fk = fromQpoly(K, f);
    if (prod.length !== fk.length || !prod.every((c, t) => C.polyEq(c, fk[t]))) continue;
    return { K, factors: [q1, q2] };
  }
  return null;
}

// Real closed-form root of an irreducible f over Q (used as alpha for K = Q(alpha)).
function realRootField(f, x) {
  let r;
  try { r = C.solvePolynomial(C.toTree(f, "t"), "t", {}); } catch (e) { if (e && e.code === "BUDGET") throw e; return null; }
  const root = r.exact.find((e) => e.real && (e.verified === "exact" || e.verified === "numeric"));
  if (!root) return null;
  const val = evalD(root.root, {});
  if (!Number.isFinite(val)) return null;
  // the numeric value must be a root of f
  let res = 0, sc = 0;
  for (let i = f.length - 1; i >= 0; i--) { res = res * val + N.toFloat(f[i]); sc = sc * Math.abs(val) + Math.abs(N.toFloat(f[i])); }
  if (Math.abs(res) > 1e-9 * Math.max(1, sc)) return null;
  void x;
  return new Field(f, root.root, val);
}

// ---------------------------------------------------------------- log part pieces
// integral of (B x + Cc)/(x^2 + s x + p) over K
function quadTerm(K, B, Cc, s, p, x) {
  const out = [];
  const q = canon(X.add(X.pow(x, X.TWO), X.mul(K.tree(s), x), K.tree(p)));
  const delta = K.sub(K.mul(K.q(4), p), K.mul(s, s)); // 4p - s^2
  const dv = K.value(delta);
  if (!Number.isFinite(dv) || Math.abs(dv) < 1e-12) throw unsupported("cannot decide the sign of a discriminant");
  const k2 = K.sub(K.mul(K.q(2), Cc), K.mul(B, s)); // 2C - B s
  if (dv > 0) {
    if (!K.zero(B)) out.push(X.mul(K.tree(K.mul(B, K.q(N.HALF))), X.fn("ln", q)));
    if (!K.zero(k2)) {
      const sd = canon(X.sqrt(K.tree(delta)));
      out.push(X.mul(K.tree(k2), X.pow(sd, X.NEG_ONE), X.fn("atan", X.mul(X.add(X.mul(X.TWO, x), K.tree(s)), X.pow(sd, X.NEG_ONE)))));
    }
  } else {
    const D = K.neg(delta); // s^2 - 4p > 0
    if (!K.zero(B)) out.push(X.mul(K.tree(K.mul(B, K.q(N.HALF))), X.fn("ln", X.fn("abs", q))));
    if (!K.zero(k2)) {
      const sd = canon(X.sqrt(K.tree(D)));
      const u = X.add(x, K.tree(K.mul(s, K.q(N.HALF))));
      const hsd = canon(X.mul(X.HALF, sd));
      out.push(X.mul(K.tree(k2), X.pow(X.mul(X.TWO, sd), X.NEG_ONE),
        X.fn("ln", X.fn("abs", X.mul(X.add(u, X.neg(hsd)), X.pow(X.add(u, hsd), X.NEG_ONE))))));
    }
  }
  return out;
}

// integral of A/f over K where f (over K) is squarefree, deg A < deg f; f given monic-able.
function logPartK(K, A, f, x, depth = 0) {
  if (depth > 3) throw unsupported("field tower too deep");
  const lcInv = K.inv(f[f.length - 1]);
  f = pscale(K, f, lcInv);
  A = pscale(K, A, lcInv);
  const d = f.length - 1;
  if (d === 1) {
    // A / (x + f0)
    const c = A[0] || [];
    if (K.zero(c)) return [];
    return [X.mul(K.tree(c), X.fn("ln", X.fn("abs", canon(X.add(x, K.tree(f[0]))))))];
  }
  if (d === 2) return quadTerm(K, A[1] || [], A[0] || [], f[1], f[0], x);
  if (!K.isQ()) throw unsupported("irreducible factor of degree > 2 over an extension field");
  throw unsupported("irreducible factor of degree > 2");
}

// integral of A/f over Q, f irreducible over Q, deg A < deg f
function logPartIrreducible(A, f, x, log) {
  const d = f.length - 1;
  const KQ = Field.Q();
  if (d <= 2) return logPartK(KQ, fromQpoly(KQ, A), fromQpoly(KQ, f), x);
  // Rothstein-Trager: R(t) = res_x(f, A - t f')
  const vars = ["x", "t"];
  const toM = (p) => C.mpoly(vars, p.map((c, i) => [[i, 0], c]).filter(([, c]) => c.n !== 0n));
  const fM = toM(f), AM = toM(A), dfM = toM(C.deriv(f));
  const tM = C.mVar(vars, "t");
  const R = C.mResultant(fM, C.mSub(AM, C.mMul(tM, dfM)), "x");
  const Rt = C.mToU(C.mReorder(R, vars), "t");
  const fq = C.factorQ(Rt);
  if (fq.factors.every(({ poly }) => poly.length === 2)) {
    const out = [];
    for (const { poly } of fq.factors) {
      const c = N.div(N.neg(poly[0]), poly[1]);
      const v = C.gcd(f, C.sub(A, C.scale(C.deriv(f), c)));
      if (v.length > 1) out.push(X.mul(X.num(c), X.fn("ln", X.fn("abs", qtree(v, x)))));
    }
    log && log.add({ rule: "int.risch", title: "Rothstein-Trager logarithmic part", why: `The resultant res_x(f, A - t f') = ${C.toTree(Rt, "t") && ""}has only rational roots, so the logarithmic part is a sum of c ln|gcd(f, A - c f')| with rational c.`, before: X.integral(X.div(qtree(A, x), qtree(f, x)), x), after: canon(X.add(...out)) });
    return out;
  }
  // split over a real field
  const fm = C.monic(f);
  if (d === 4) {
    const sp = splitQuarticSqrt(fm);
    if (sp) {
      const { K, factors: [q1, q2] } = sp;
      const Ak = pscale(K, fromQpoly(K, A), K.q(N.inv(C.lc(f))));
      // partial fractions over K: A/(q1 q2) = R1/q1 + R2/q2
      const { s, t } = pxgcd(K, q2, q1); // s q2 + t q1 = 1
      const R1 = pdivmod(K, pmul(K, Ak, s), q1).r;
      const R2 = pdivmod(K, pmul(K, Ak, t), q2).r;
      log && log.add({ rule: "int.partial", title: "Factor over a real quadratic field", why: `${X.freeSymbols(qtree(f, x)).size ? "" : ""}The quartic ${printPoly(f, x)} is irreducible over Q but splits into two real quadratics over Q(sqrt(${N.toString(N.neg(K.m[0]))})); partial fractions are computed there exactly.`, before: qtree(f, x), after: canon(X.mul(ptree(K, q1, x), ptree(K, q2, x))) });
      return [...logPartK(K, R1, q1, x), ...logPartK(K, R2, q2, x)];
    }
  }
  if (d === 3) {
    const K = realRootField(fm, x);
    if (K) {
      const fk = fromQpoly(K, fm);
      const alpha = [Q0, Q1];
      const lin = [K.neg(alpha), K.q(1)]; // x - alpha
      const { q: g, r } = pdivmod(K, fk, lin);
      if (r.length) throw new Error("Quelvra: internal error (root division)");
      const Ak = pscale(K, fromQpoly(K, A), K.q(N.inv(C.lc(f))));
      const c = K.div(peval(K, Ak, alpha), peval(K, g, alpha));
      const Bq = pdivmod(K, psub(K, Ak, pscale(K, g, c)), lin);
      if (Bq.r.length) throw new Error("Quelvra: internal error (partial fractions over K)");
      log && log.add({ rule: "int.partial", title: "Split the cubic at its real root", why: `The cubic ${printPoly(f, x)} is irreducible over Q; with its real root a = ${printT(K.alpha)} it factors exactly as (x - a) times a quadratic over Q(a).`, before: qtree(f, x), after: canon(X.mul(X.add(x, X.neg(K.alpha)), ptree(K, g, x))) });
      const out = [];
      if (!K.zero(c)) out.push(X.mul(K.tree(c), X.fn("ln", X.fn("abs", canon(X.add(x, X.neg(K.alpha)))))));
      out.push(...logPartK(K, Bq.q, g, x, 1));
      return out;
    }
  }
  throw unsupported(`the denominator has an irreducible factor of degree ${d} that Quelvra cannot split into real factors exactly`);
}
function printPoly(p, x) { return printT(qtree(p, x)); }
let printT = (t) => String(t && t.k);
export function setPrinter(fn) { printT = fn; }

// ---------------------------------------------------------------- entry
// integral of num/den (UPoly over Q) in x. Returns tree or throws UNSUPPORTED.
export function integrateRationalQ(num, den, x, log) {
  num = C.norm(num); den = C.norm(den);
  if (!den.length) throw unsupported("zero denominator");
  if (!num.length) return X.ZERO;
  const g0 = C.gcd(num, den);
  if (g0.length > 1) { num = C.exactDiv(num, g0); den = C.exactDiv(den, g0); }
  // normalise den monic
  const lcd = C.lc(den);
  num = C.scale(num, N.inv(lcd)); den = C.monic(den);
  const { q: polyPart, r: rest } = C.divmod(num, den);
  const terms = [];
  if (polyPart.length) {
    const P = [Q0, ...polyPart.map((c, i) => N.div(c, N.Q(i + 1)))];
    terms.push(qtree(C.norm(P), x));
  }
  if (!rest.length) return canon(X.add(...terms));
  // Hermite
  const h = hermite(rest, den);
  const ratPart = h.parts.map(({ num: a, den: b }) => X.mul(qtree(a, x), X.pow(qtree(b, x), X.NEG_ONE)));
  if (ratPart.length) {
    const rp = canon(X.add(...ratPart));
    terms.push(rp);
    log && log.add({ rule: "int.partial", title: "Hermite reduction (rational part)", why: "The denominator has repeated factors. Hermite reduction splits off the rational part of the antiderivative exactly, leaving an integrand with a squarefree denominator.", before: X.integral(canon(X.div(qtree(rest, x), qtree(den, x))), x), after: canon(X.add(rp, X.integral(canon(X.div(qtree(h.A, x), qtree(h.D, x))), x))) });
  }
  let A = h.A, D = h.D;
  const dv = C.divmod(A, D);
  if (dv.q.length) {
    const P = [Q0, ...dv.q.map((c, i) => N.div(c, N.Q(i + 1)))];
    terms.push(qtree(C.norm(P), x));
    A = dv.r;
  }
  if (A.length) {
    const ap = C.apartTerms(A, D);
    if (ap.terms.length > 1 || (ap.terms[0] && ap.terms[0].factor.length > 2)) {
      log && log.add({ rule: "int.partial", title: "Partial fractions", why: "Factor the denominator over Q and split the fraction into simple fractions over its irreducible factors.", before: canon(X.div(qtree(A, x), qtree(D, x))), after: canon(X.add(...ap.terms.map((t) => X.mul(qtree(t.numer, x), X.pow(qtree(t.factor, x), X.num(-t.power)))))) });
    }
    for (const t of ap.terms) {
      if (t.power !== 1) throw new Error("Quelvra: internal error (squarefree denominator expected)");
      terms.push(...logPartIrreducible(t.numer, t.factor, x, log));
    }
  }
  return canon(X.add(...terms));
}
