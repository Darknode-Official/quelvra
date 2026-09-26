// Quelvra integration: exponential polynomials (Risch differential equation) and classic
// non-elementary integrals.
//
// expPolyRisch(f, x): f = R(x) e^(q(x)) with R rational and q polynomial over Q.
//   Theorem (Liouville / Risch): the integral is elementary iff y' + q' y = R has a rational solution y,
//   and then it equals y e^q. The solution is searched with exact linear algebra over Q:
//     * a simple pole of R cannot be produced by y' + q' y (a pole of order k of y gives order k + 1),
//       so simple poles prove non-elementarity;
//     * otherwise y = Y / V with V = prod B_i^(i-1) (squarefree decomposition of the denominator of R)
//       and a degree bound for Y; an inconsistent linear system proves non-elementarity.
//   When not elementary, the classic special functions are used where they apply:
//     q of degree 2          ->  y e^q + c * integral of e^q  = erf / erfi
//     q of degree 1          ->  simple poles at rational points give Ei(a (x - r)) terms
//   and otherwise NONELEMENTARY is reported with the proof.
//
// specialIntegral(f, x): sin(u)/v, cos(u)/v (Si, Ci), sinh/cosh (Shi, Chi), sin/cos of a quadratic
//   (Fresnel), with reduction formulas for higher powers of v.

import * as X from "../expr.js";
import * as N from "../num.js";
import * as P from "../poly.js";
import { canon, polyCoeffs, linearCoeffs, evalD } from "./int-util.js";

const { ZERO, ONE, TWO, NEG_ONE, HALF, E, PI } = X;

// ---------------------------------------------------------------- exact linear algebra over Q
// rows: Rational[][] (m x n), rhs: Rational[] -> solution Rational[] (free variables 0) or null.
export function solveLinearQ(rows, rhs) {
  const m = rows.length, n = m ? rows[0].length : 0;
  const A = rows.map((r, i) => [...r, rhs[i]]);
  const piv = [];
  let r = 0;
  for (let c = 0; c < n && r < m; c++) {
    let p = -1;
    for (let i = r; i < m; i++) if (A[i][c].n !== 0n) { p = i; break; }
    if (p < 0) continue;
    [A[r], A[p]] = [A[p], A[r]];
    const inv = N.inv(A[r][c]);
    for (let j = c; j <= n; j++) A[r][j] = N.mul(A[r][j], inv);
    for (let i = 0; i < m; i++) {
      if (i === r || A[i][c].n === 0n) continue;
      const k = A[i][c];
      for (let j = c; j <= n; j++) A[i][j] = N.sub(A[i][j], N.mul(k, A[r][j]));
    }
    piv.push(c);
    r++;
  }
  for (let i = r; i < m; i++) if (A[i][n].n !== 0n) return null;
  const sol = Array.from({ length: n }, () => N.ZERO);
  piv.forEach((c, i) => { sol[c] = A[i][n]; });
  return sol;
}

// ---------------------------------------------------------------- recognise R(x) e^(q(x))
// Returns { R: tree, q: tree } with q polynomial of degree >= 1 over Q, R rational over Q; or null.
function splitExp(f, x) {
  const fac = f.k === "mul" ? f.args : [f];
  const ex = [], rest = [];
  for (const w of fac) {
    if (w.k === "pow" && w.args[0] === E && !X.freeOf(w.args[1], x)) ex.push(w.args[1]);
    else rest.push(w);
  }
  if (!ex.length) return null;
  const q = canon(X.add(...ex));
  const R = canon(X.mul(...rest));
  return { R, q };
}
function ratQ(R, x) {
  const [n, d] = P.numDen(R);
  let pn, pd;
  try { pn = P.fromTree(n, x.name); pd = P.fromTree(d, x.name); } catch (e) { if (e && e.code === "BUDGET") return null; throw e; }
  if (!pn || !pd || !pd.length) return null;
  const g = P.gcd(pn, pd);
  if (g.length > 1) { pn = P.exactDiv(pn, g); pd = P.exactDiv(pd, g); }
  const l = P.lc(pd);
  return { A: P.scale(pn, N.inv(l)), B: P.monic(pd) };
}

// Solve Bd (Y' V - Y V' + q' Y V) = A V^2 - Bd V^2 * extra for Y of degree <= deg, with extra
// unknown terms (each a known rational function e_k with unknown coefficient c_k):
// y' + q' y = A/Bd - sum c_k e_k.  extras: [{num, den}] (UPolys).
function solveRDE(A, Bd, V, qd, deg, extras = []) {
  if (deg < 0 && !extras.length) return null;
  const nY = Math.max(0, deg + 1);
  // common multiplier M = Bd V^2 * prod(extra dens)  -> polynomial identity
  let M = P.mul(Bd, P.mul(V, V));
  for (const e of extras) M = P.lcm(M, P.mul(e.den, P.mul(V, V)));
  const Mv2 = P.exactDiv(M, P.mul(V, V)); // multiplier for (Y' V - Y V' + q' Y V)
  const columns = [];
  for (let j = 0; j < nY; j++) {
    const Y = Array.from({ length: j + 1 }, (_, i) => (i === j ? N.ONE : N.ZERO));
    const term = P.add(P.sub(P.mul(P.deriv(Y), V), P.mul(Y, P.deriv(V))), P.mul(P.mul(qd, Y), V));
    columns.push(P.mul(Mv2, term));
  }
  for (const e of extras) columns.push(P.mul(P.exactDiv(M, e.den), e.num)); // + c_k e_k * M
  const rhsPoly = P.mul(P.exactDiv(M, Bd), A);
  let len = rhsPoly.length;
  for (const c of columns) len = Math.max(len, c.length);
  if (len > 400) return null;
  const rows = [], rhs = [];
  for (let i = 0; i < len; i++) {
    rows.push(columns.map((c) => c[i] || N.ZERO));
    rhs.push(rhsPoly[i] || N.ZERO);
  }
  const sol = solveLinearQ(rows, rhs);
  if (!sol) return null;
  return { Y: P.norm(sol.slice(0, nY)), c: sol.slice(nY) };
}

const ptree = (p, x) => P.toTree(p, x.name);

export function expPolyRisch(f, x, eng) {
  // group terms that share the same exponential
  const terms = f.k === "add" ? f.args : [f];
  let q = null;
  const Rs = [];
  for (const t of terms) {
    const s = splitExp(t, x);
    if (!s) return null;
    if (q && s.q !== q) return null;
    q = s.q;
    Rs.push(s.R);
  }
  const qc = polyCoeffs(q, x);
  if (!qc || qc.length < 2 || !qc.every(X.isNum)) return null;
  const qp = P.norm(qc.map((t) => t.v));
  const dq = qp.length - 1;
  const R = canon(X.add(...Rs));
  const rq = ratQ(R, x);
  if (!rq) return null;
  const { A, B: Bd } = rq;
  if (!A.length) return null;
  const qd = P.deriv(qp);
  const eq = X.exp(q);
  // squarefree decomposition of Bd
  const sf = Bd.length > 1 ? P.squareFree(Bd).factors : [];
  let V = [N.ONE], simple = [N.ONE];
  for (const { poly, mult } of sf) {
    if (mult >= 2) V = P.mul(V, P.pow(poly, mult - 1));
    else simple = P.mul(simple, poly);
  }
  const degR = (A.length - 1) - (Bd.length - 1);
  const degY = degR - (dq - 1) + (V.length - 1);
  const proofBase = `By Liouville's theorem (the Risch algorithm for an exponential), the integral of R e^q with q = ${show(q)} is elementary exactly when y' + q' y = R has a rational solution y.`;
  if (simple.length === 1) {
    const s = solveRDE(A, Bd, V, qd, degY);
    if (s) {
      const y = canon(X.div(ptree(s.Y, x), ptree(V, x)));
      const F = canon(X.mul(y, eq));
      return { F, title: "Risch differential equation", why: `${proofBase} Solving it with exact linear algebra gives y = ${show(y)}, so the antiderivative is y e^q.` };
    }
  }
  // not elementary; special functions where possible
  if (dq === 2 && Bd.length === 1) {
    // y polynomial of degree deg R - 1, plus a constant remainder c: y' + q' y = R - c
    const deg = A.length - 2;
    const s = solveRDE(A, Bd, [N.ONE], qd, deg, [{ num: [N.ONE], den: [N.ONE] }]);
    if (!s) return null;
    const c = s.c[0];
    const y = ptree(s.Y, x);
    const [q0, q1, q2] = qp;
    // integral of e^(q2 (x + h)^2 + k)
    const h = N.div(q1, N.mul(N.Q(2), q2)), k = N.sub(q0, N.div(N.mul(q1, q1), N.mul(N.Q(4), q2)));
    const w = X.add(x, X.num(h));
    const aa = N.abs(q2);
    const sa = X.sqrt(X.num(aa));
    const fname = N.isNeg(q2) ? "erf" : "erfi";
    const G = X.mul(X.sqrt(PI), X.pow(X.mul(TWO, sa), NEG_ONE), X.exp(X.num(k)), X.fn(fname, X.mul(sa, w)));
    const F = canon(X.add(X.mul(y, eq), X.mul(X.num(c), G)));
    const proof = `${proofBase} Here y would have to be a polynomial, and comparing coefficients leaves the constant ${N.toString(c)} unmatched, so no such y exists.`;
    if (c.n === 0n) return null; // would have been elementary
    return { F, special: true, nonelementary: true, proof, title: `Non-elementary: express with ${fname}`, why: `${proof} The remainder ${N.toString(c)} e^q integrates to the ${fname === "erf" ? "error function" : "imaginary error function"}: e^(-a w^2) dw = sqrt(pi)/(2 sqrt(a)) erf(sqrt(a) w), e^(a w^2) dw = sqrt(pi)/(2 sqrt(a)) erfi(sqrt(a) w).` };
  }
  if (dq === 1) {
    // simple poles at rational points -> Ei terms: y' + a y = R - sum c_r/(x - r)
    const a = qp[1];
    const lin = [];
    for (const { poly, mult } of sf) {
      if (mult !== 1) continue;
      const fq = P.factorQ(poly);
      for (const { poly: g } of fq.factors) {
        if (g.length !== 2) return { nonelementary: true, proof: `${proofBase} R has a simple pole at an irrational point, so no rational y exists.` };
        lin.push(N.div(N.neg(g[0]), g[1]));
      }
    }
    // poles of higher order at the same points are allowed in y
    const extras = lin.map((r) => ({ num: [N.ONE], den: [N.neg(r), N.ONE] }));
    const s = solveRDE(A, Bd, V, qd, degY, extras);
    if (!s) return null;
    const y = canon(X.div(ptree(s.Y, x), ptree(V, x)));
    const eis = [];
    lin.forEach((r, i) => {
      const c = s.c[i];
      if (c.n === 0n) return;
      // integral of c e^(a x + b)/(x - r) = c e^(a r + b) Ei(a (x - r))
      eis.push(X.mul(X.num(c), X.exp(canon(X.subs(q, { [x.name]: X.num(r) }))), X.fn("Ei", X.mul(X.num(a), X.sub(x, X.num(r))))));
    });
    if (!eis.length) return null;
    const F = canon(X.add(X.mul(y, eq), ...eis));
    const proof = `${proofBase} R has a simple pole, and a pole of order k of y gives a pole of order k + 1 of y' + q' y, so no rational y exists.`;
    return { F, special: true, nonelementary: true, proof, title: "Non-elementary: express with the exponential integral Ei", why: `${proof} Each simple pole c/(x - r) contributes c e^(q(r)) Ei(a (x - r)), since d/dx Ei(u) = e^u/u.` };
  }
  const proof = simple.length > 1
    ? `${proofBase} R has a simple pole, which y' + q' y cannot produce, so no rational y exists.`
    : `${proofBase} The linear system for y (degree bound from the leading terms) is inconsistent, so no rational y exists.`;
  return { nonelementary: true, proof };
}

function show(u) {
  try { return SHOW(u); } catch (_) { return "?"; }
}
let SHOW = (u) => String(u.k);
export function setShow(fn) { SHOW = fn; }

// ---------------------------------------------------------------- Si, Ci, Shi, Chi, Fresnel
export function specialIntegral(f, x, eng) {
  const fac = f.k === "mul" ? f.args : [f];
  const cst = fac.filter((w) => X.freeOf(w, x));
  const vary = fac.filter((w) => !X.freeOf(w, x));
  const c = cst.length ? canon(X.mul(...cst)) : ONE;
  // sin(q) / cos(q) with q quadratic -> Fresnel
  if (vary.length === 1 && vary[0].k === "fn" && (vary[0].name === "sin" || vary[0].name === "cos")) {
    const g = vary[0], qc = polyCoeffs(g.args[0], x);
    if (qc && qc.length === 3 && qc.every(X.isNum)) {
      const [q0, q1, q2] = qc.map((t) => t.v);
      const h = N.div(q1, N.mul(N.Q(2), q2)), k = N.sub(q0, N.div(N.mul(q1, q1), N.mul(N.Q(4), q2)));
      const w = X.add(x, X.num(h));
      const aa = N.abs(q2), sg = N.isNeg(q2) ? NEG_ONE : ONE;
      // integral of sin(a w^2) = sqrt(pi/(2a)) S(sqrt(2a/pi) w), cos -> C
      const scale = X.sqrt(X.div(PI, X.mul(TWO, X.num(aa))));
      const arg = X.mul(X.sqrt(X.div(X.mul(TWO, X.num(aa)), PI)), w);
      const S = X.mul(sg, scale, X.fn("FresnelS", arg)), Cc = X.mul(scale, X.fn("FresnelC", arg));
      // sin(s a w^2 + k) = sin(s a w^2) cos k + cos(a w^2) sin k
      const K = X.num(k);
      const F = g.name === "sin" ? X.add(X.mul(S, X.fn("cos", K)), X.mul(Cc, X.fn("sin", K))) : X.sub(X.mul(Cc, X.fn("cos", K)), X.mul(S, X.fn("sin", K)));
      return { F: canon(X.mul(c, F)), title: "Fresnel integral", why: "sin and cos of a quadratic have no elementary antiderivative; by definition FresnelS(z) = integral of sin(pi t^2/2) from 0 to z and FresnelC(z) = integral of cos(pi t^2/2), so after completing the square the integral is a combination of them.", proof: "Integrals of sin(a x^2 + b x + c) and cos(a x^2 + b x + c) are not elementary (Liouville; they are e^(i q)-integrals of Risch type with deg q = 2)." };
    }
  }
  // trig(u) / v^n with u, v linear and proportional
  if (vary.length === 2) {
    let tf = null, pw = null;
    for (const w of vary) {
      if (w.k === "fn" && ["sin", "cos", "sinh", "cosh"].includes(w.name)) tf = w;
      else if (w.k === "pow" && X.isInt(w.args[1]) && w.args[1].v.n < 0n) pw = w;
    }
    if (tf && pw) {
      const v = pw.args[0], n = Number(-pw.args[1].v.n);
      const Lu = tf.args[0] === x ? [ONE, ZERO] : linearCoeffs(tf.args[0], x);
      const Lv = v === x ? [ONE, ZERO] : linearCoeffs(v, x);
      if (Lu && Lv && n >= 1 && n <= 8) {
        const r = trigOverLinear(tf.name, tf.args[0], Lu, v, Lv, n, x);
        if (r) return { F: canon(X.mul(c, r)), title: `Express with ${tf.name === "sin" ? "Si" : tf.name === "cos" ? "Ci" : tf.name === "sinh" ? "Shi" : "Chi"}`, why: `${tf.name}(u)/u has no elementary antiderivative; by definition Si(z) = integral of sin(t)/t from 0 to z, Ci'(z) = cos(z)/z, Shi'(z) = sinh(z)/z, Chi'(z) = cosh(z)/z. Higher powers of the denominator are reduced by integration by parts.${n > 1 ? "" : ""}`, proof: `The integral of ${tf.name}(x)/x is not elementary (Liouville).` };
      }
    }
  }
  void eng; void evalD; void HALF;
  return null;
}

// integral of trig(u)/v^n with u = a x + b, v = p x + r (u = k v + d)
function trigOverLinear(name, u, [a, b], v, [p, r], n, x) {
  const k = canon(X.div(a, p));
  const d = canon(X.sub(b, X.mul(k, r)));
  const kv = canon(X.mul(k, v));
  const other = { sin: "cos", cos: "sin", sinh: "cosh", cosh: "sinh" }[name];
  const hyper = name === "sinh" || name === "cosh";
  if (n === 1) {
    // sin(kv + d) = sin(kv) cos d + cos(kv) sin d ; cos(kv + d) = cos(kv) cos d - sin(kv) sin d
    const Si = X.fn(hyper ? "Shi" : "Si", kv), Ci = X.fn(hyper ? "Chi" : "Ci", X.fn("abs", kv));
    const cd = X.fn(hyper ? "cosh" : "cos", d), sd = X.fn(hyper ? "sinh" : "sin", d);
    let F;
    if (name === "sin") F = X.add(X.mul(Si, cd), X.mul(Ci, sd));
    else if (name === "cos") F = X.sub(X.mul(Ci, cd), X.mul(Si, sd));
    else if (name === "sinh") F = X.add(X.mul(Si, cd), X.mul(Ci, sd));
    else F = X.add(X.mul(Ci, cd), X.mul(Si, sd));
    // Ci(|kv|) only makes sense when k != 0
    return canon(X.div(F, p));
  }
  // reduction: trig(u)/v^n dx = -trig(u)/((n-1) p v^(n-1)) + a/((n-1) p) integral trig'(u)/v^(n-1)
  const sign = name === "cos" ? NEG_ONE : ONE; // (cos)' = -sin
  const lower = trigOverLinear(other, u, [a, b], v, [p, r], n - 1, x);
  if (!lower) return null;
  return canon(X.add(
    X.mul(NEG_ONE, X.fn(name, u), X.pow(X.mul(X.num(n - 1), p, X.pow(v, X.num(n - 1))), NEG_ONE)),
    X.mul(sign, a, X.pow(X.mul(X.num(n - 1), p), NEG_ONE), lower)));
}
