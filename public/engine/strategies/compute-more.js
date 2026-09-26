// More command strategies: data statistics beyond mean/median (population forms, quartiles, IQR,
// range, weighted mean, correlation, regression), the inverse normal, base conversion and
// polynomial commands (division, remainder, gcd, coefficients, discriminant, vertex).
//
// Every command is checked by an independent route: floating-point recomputation by a different
// formula, a defining property (q d + r = p, the gcd divides both inputs, the cdf at the quantile
// equals p), or a built-in conversion. A failed or impossible check withholds the answer.

import * as X from "../expr.js";
import * as Nm from "../num.js";
import { simplify, expand } from "../simplify.js";
import { toText } from "../print.js";
import * as L from "../linalg.js";
import * as T from "../numtheory.js";
import * as St from "../stats.js";
import * as P from "../poly.js";
import { equivalent, evalReal, evalC } from "../verify.js";
import { DISCRETE_FLOAT } from "../verify-discrete.js";
import { toContractVerification, unsupported, solve as solveTree } from "../orchestrate.js";
import { complexParts } from "../calc/cutil.js";
import { diff as diffFn } from "../calc/diff.js";
import { definiteIntegral } from "../calc/int-definite.js";

const V = (status, detail, name = "check") => toContractVerification([{ status, checks: [{ kind: name, ok: status !== "failed", detail }] }]);
const exact = (tree, extra = {}) => ({ answers: [{ kind: "exact", tree, ...extra }], solutionStatus: "exact" });
const close = (a, b, tol = 1e-9) => Number.isFinite(a) && Number.isFinite(b) && Math.abs(a - b) <= tol * Math.max(1, Math.abs(a), Math.abs(b));
const numCheck = (want, tree, what) => {
  const got = L.evalFloat(simplify(tree));
  return V(close(want, got) ? "verified-numeric" : "failed", `independent floating-point ${what} (${+want.toPrecision(12)}) agrees`, "recompute");
};
const isList = (a) => a && (a.k === "tuple" || a.k === "set" || a.k === "vector" || a.k === "matrix");
function listOf(u) {
  const s = u.k === "matrix" && u.args.length === 1 && u.args[0].args ? u.args[0] : u;
  const xs = (isList(s) ? s.args : [s]).map((a) => simplify(a));
  if (!xs.length || !xs.every((a) => X.isNum(a))) throw unsupported("statistics need a list of numbers");
  return xs.map((a) => a.v);
}
const dataArgs = (node) => (node.args.length === 1 && isList(node.args[0]) ? listOf(node.args[0]) : node.args.flatMap(listOf));
const floats = (vs) => vs.map((v) => Nm.toFloat(v));
const fmean = (a) => a.reduce((s, x) => s + x, 0) / a.length;
// independent quartiles: sort floats, split at the middle (median excluded when n is odd)
function fquart(a) {
  const s = a.slice().sort((x, y) => x - y), n = s.length;
  const med = (t) => (t.length % 2 ? t[(t.length - 1) / 2] : (t[t.length / 2 - 1] + t[t.length / 2]) / 2);
  if (n < 2) return [s[0], s[0], s[0]];
  return [med(s.slice(0, Math.floor(n / 2))), med(s), med(s.slice(Math.ceil(n / 2)))];
}
const QNOTE = "Quartiles by the median-of-halves method (as on TI calculators): Q1 and Q3 are the medians of the lower and upper halves, leaving out the middle value when the count is odd. Other textbooks interpolate and can give slightly different values.";

// Polynomials: the variable is the single free symbol (or x), coefficients must be rational.
function polyVar(nodes, given) {
  if (given) { if (given.k !== "sym") throw unsupported("the variable must be a single letter"); return given.name; }
  const fs = new Set();
  for (const n of nodes) for (const s of X.freeSymbols(n)) fs.add(s);
  if (fs.size > 1) throw unsupported(`several variables (${[...fs].join(", ")}); name the variable as the last argument`);
  return fs.size ? [...fs][0] : "x";
}
function polyOf(u, x) {
  const p = P.fromTree(simplify(u), x);
  if (!p) throw unsupported(`${toText(u)} is not a polynomial in ${x} with rational coefficients`);
  return p;
}
const degOf = (p) => p.length - 1;
const eqv = (a, b) => { const e = equivalent(expand(a), expand(b)); return e.status.startsWith("equivalent") ? (e.status === "equivalent-exact" ? "verified-exact" : "verified-numeric") : "failed"; };
function divParts(node) {
  if (node.args.length < 2) throw unsupported("give the dividend and the divisor, e.g. polydiv(x^3 - 1, x - 1)");
  const [a, b, v] = node.args;
  const x = polyVar([a, b], v);
  const pa = polyOf(a, x), pb = polyOf(b, x);
  if (!pb.length) throw unsupported("division by the zero polynomial");
  const { q, r } = P.divmod(pa, pb);
  return { a, b, x, pb, Q: P.toTree(q, x), R: P.toTree(r, x) };
}
function divCheck({ a, b, x, pb, Q, R }) {
  // q d + r must expand back to p, and deg r < deg d (checked on the result, not the algorithm)
  const back = eqv(X.add(X.mul(Q, b), R), a);
  const rp = P.fromTree(R, x);
  const small = rp && (rp.length === 0 || degOf(rp) < degOf(pb));
  return V(back !== "failed" && small ? back : "failed", "quotient x divisor + remainder expands back to the dividend, and the remainder has lower degree than the divisor", "division-identity");
}

const sideOf = (u) => (u.k === "eq" ? X.sub(u.args[0], u.args[1]) : u);
// rational coefficient c of x^i y^j in a polynomial in x and y, or null
function xyCoeffs(u) {
  const e = expand(simplify(sideOf(u)));
  const cx = P.coefficients(e, "x");
  if (!cx) return null;
  const out = new Map();
  for (let i = 0; i < cx.length; i++) {
    if (!cx[i]) continue;
    const cy = P.coefficients(cx[i], "y");
    if (!cy) return null;
    for (let j = 0; j < cy.length; j++) {
      if (!cy[j]) continue;
      const c = simplify(cy[j]);
      if (c === X.ZERO) continue;
      if (!X.isNum(c)) return null;
      out.set(`${i},${j}`, c.v);
    }
  }
  return out;
}
const cf = (m, k) => m.get(k) || Nm.ZERO;

export const MORE_COMMANDS = {
  pstdev(node) {
    const vs = dataArgs(node);
    const tree = simplify(St.stdDev(vs, { population: true }));
    return { ...exact(tree), verify: () => { const f = floats(vs), m = fmean(f); return numCheck(Math.sqrt(f.reduce((s, x) => s + x * x, 0) / f.length - m * m), tree, "population standard deviation"); } };
  },
  pvariance(node) {
    const vs = dataArgs(node);
    const tree = simplify(St.variance(vs, { population: true }));
    return { ...exact(tree), verify: () => { const f = floats(vs), m = fmean(f); return numCheck(f.reduce((s, x) => s + x * x, 0) / f.length - m * m, tree, "population variance"); } };
  },
  quartiles(node) {
    const vs = dataArgs(node);
    const q = St.quartiles(vs);
    const trees = [q.q1, q.q2, q.q3].map((t) => simplify(t));
    return {
      answers: trees.map((t, i) => ({ kind: "exact", tree: t, label: ["Q1", "Q2 (median)", "Q3"][i] })), solutionStatus: "exact", note: QNOTE,
      verify: () => {
        const w = fquart(floats(vs));
        const ok = trees.every((t, i) => close(w[i], L.evalFloat(t)));
        return V(ok ? "verified-numeric" : "failed", `independent quartiles ${w.map((v) => +v.toPrecision(10)).join(", ")} agree`, "recompute");
      },
    };
  },
  iqr(node) {
    const vs = dataArgs(node);
    const tree = simplify(St.iqr(vs));
    return { ...exact(tree), note: QNOTE, verify: () => { const w = fquart(floats(vs)); return numCheck(w[2] - w[0], tree, "interquartile range"); } };
  },
  datarange(node) {
    const vs = dataArgs(node);
    const tree = simplify(St.range(vs));
    return { ...exact(tree), verify: () => { const f = floats(vs); return numCheck(Math.max(...f) - Math.min(...f), tree, "range (max - min)"); } };
  },
  wmean(node) {
    if (node.args.length !== 2) throw unsupported("give the values and the weights as two lists, e.g. wmean([80, 90], [1, 3])");
    const vs = listOf(node.args[0]), ws = listOf(node.args[1]);
    if (vs.length !== ws.length) throw unsupported("the values and the weights have different lengths");
    let s = Nm.ZERO, w = Nm.ZERO;
    vs.forEach((v, i) => { s = Nm.add(s, Nm.mul(v, ws[i])); w = Nm.add(w, ws[i]); });
    if (Nm.isZero(w)) throw unsupported("the weights add up to zero");
    const tree = X.num(Nm.div(s, w));
    return { ...exact(tree), verify: () => {
      const f = floats(vs), g = floats(ws);
      let num = 0, den = 0;
      for (let i = f.length - 1; i >= 0; i--) { num += f[i] * g[i]; den += g[i]; }
      return numCheck(num / den, tree, "weighted mean");
    } };
  },
  corr(node) {
    if (node.args.length !== 2) throw unsupported("give the x and y data as two lists, e.g. corr([1, 2, 3], [2, 4, 7])");
    const xs = listOf(node.args[0]), ys = listOf(node.args[1]);
    const tree = simplify(St.correlation(xs, ys));
    return { ...exact(tree), verify: () => {
      // independent: r = (n sum xy - sum x sum y) / sqrt((n sum x^2 - (sum x)^2)(n sum y^2 - (sum y)^2))
      const a = floats(xs), b = floats(ys), n = a.length;
      let sx = 0, sy = 0, sxx = 0, syy = 0, sxy = 0;
      for (let i = 0; i < n; i++) { sx += a[i]; sy += b[i]; sxx += a[i] * a[i]; syy += b[i] * b[i]; sxy += a[i] * b[i]; }
      return numCheck((n * sxy - sx * sy) / Math.sqrt((n * sxx - sx * sx) * (n * syy - sy * sy)), tree, "Pearson correlation");
    } };
  },
  linreg(node) {
    if (node.args.length !== 2) throw unsupported("give the x and y data as two lists, e.g. linreg([1, 2, 3], [2, 4, 7])");
    const xs = listOf(node.args[0]), ys = listOf(node.args[1]);
    const r = St.linearRegression(xs, ys);
    const m = simplify(r.slope), c = simplify(r.intercept);
    const eqn = X.eq(X.sym("y"), simplify(X.add(X.mul(m, X.sym("x")), c)));
    return {
      answers: [{ kind: "exact", tree: eqn, label: "Least-squares line" }, { kind: "exact", tree: m, label: "slope" }, { kind: "exact", tree: c, label: "intercept" }],
      solutionStatus: "exact",
      verify: () => {
        // independent: solve the 2x2 normal equations [n sx; sx sxx][c; m] = [sy; sxy] by Cramer's rule
        const a = floats(xs), b = floats(ys), n = a.length;
        let sx = 0, sy = 0, sxx = 0, sxy = 0;
        for (let i = 0; i < n; i++) { sx += a[i]; sy += b[i]; sxx += a[i] * a[i]; sxy += a[i] * b[i]; }
        const det = n * sxx - sx * sx;
        const wm = (n * sxy - sx * sy) / det, wc = (sy * sxx - sx * sxy) / det;
        const ok = close(wm, L.evalFloat(m), 1e-8) && close(wc, L.evalFloat(c), 1e-8);
        return V(ok ? "verified-numeric" : "failed", `the normal equations give slope ${+wm.toPrecision(10)} and intercept ${+wc.toPrecision(10)}`, "normal-equations");
      },
    };
  },
  invnorm(node) {
    const a = node.args.map((t) => L.evalFloat(simplify(t)));
    if (!(a.length === 1 || a.length === 3) || !a.every(Number.isFinite)) throw unsupported("invnorm(p) or invnorm(p, mu, sigma) with numbers");
    const [p, mu, s] = a.length === 3 ? a : [a[0], 0, 1];
    if (!(p > 0 && p < 1)) throw unsupported("the area must be strictly between 0 and 1");
    if (!(s > 0)) throw unsupported("sigma must be positive");
    const q = St.normal(mu, s).quantile(p);
    const x = q.number !== undefined ? q.number : parseFloat(q.value);
    const value = String(+x.toPrecision(12));
    return {
      answers: [{ kind: "approx", label: `x with P(X < x) = ${+p.toPrecision(12)}`, approx: { value, digits: 12 } }], solutionStatus: "approximate",
      verify: () => {
        // independent: Simpson integration of the density up to x must give back p
        const back = DISCRETE_FLOAT.normalcdf([-Infinity, x, mu, s]);
        return V(Math.abs(back - p) <= 1e-9 ? "verified-numeric" : "failed", `integrating the normal density up to ${value} gives ${+back.toPrecision(12)}`, "cdf-roundtrip");
      },
    };
  },
  tobase(node) {
    if (node.args.length !== 2) throw unsupported("tobase(n, b), e.g. tobase(255, 16)");
    const s = simplify(node.args[0]), b = simplify(node.args[1]);
    if (!X.isInt(s) || !X.isInt(b) || b.v.n < 2n || b.v.n > 36n) throw unsupported("tobase needs an integer and a base from 2 to 36");
    const n = s.v.n, base = Number(b.v.n);
    const text = T.toBase(n, base).toUpperCase();
    return {
      answers: [{ kind: "exact", label: `${n} in base ${base}`, text: `${text} (base ${base})` }], solutionStatus: "exact",
      verify: () => {
        // independent: the built-in radix conversion for safe integers, digit-by-digit Horner otherwise
        let ok;
        if (n <= BigInt(Number.MAX_SAFE_INTEGER) && n >= -BigInt(Number.MAX_SAFE_INTEGER)) ok = Number(n).toString(base).toUpperCase() === text;
        else { let v = 0n; for (const ch of text.replace("-", "")) v = v * BigInt(base) + BigInt(parseInt(ch, 36)); ok = (text.startsWith("-") ? -v : v) === n; }
        return V(ok ? "verified-exact" : "failed", "an independent radix conversion gives the same digits", "radix");
      },
    };
  },
  frombase(node) {
    if (node.args.length !== 2) throw unsupported("frombase(digits, b), e.g. frombase(1011, 2)");
    const s = simplify(node.args[0]), b = simplify(node.args[1]);
    if (!X.isInt(s) || !X.isInt(b) || b.v.n < 2n || b.v.n > 10n) throw unsupported("frombase takes decimal digits and a base from 2 to 10; for letter digits write the number as 0x... or ask in words");
    const digits = s.v.n.toString(), base = Number(b.v.n);
    for (const ch of digits.replace("-", "")) if (Number(ch) >= base) throw unsupported(`the digit ${ch} is not allowed in base ${base}`);
    const v = T.fromBase(digits, base);
    return { ...exact(X.num(v)), verify: () => {
      const ok = Math.abs(Number(v)) <= Number.MAX_SAFE_INTEGER ? parseInt(digits, base) === Number(v) : T.toBase(v, base) === digits;
      return V(ok ? "verified-exact" : "failed", "an independent radix conversion gives the same value", "radix");
    } };
  },
  polydiv(node) {
    const d = divParts(node);
    return { answers: [{ kind: "exact", tree: d.Q, label: "quotient" }, { kind: "exact", tree: d.R, label: "remainder" }], solutionStatus: "exact", verify: () => divCheck(d) };
  },
  polyrem(node) {
    const d = divParts(node);
    return { ...exact(d.R, { label: "remainder" }), verify: () => divCheck(d) };
  },
  polygcd(node) {
    if (node.args.length < 2) throw unsupported("polygcd(p, q)");
    const [a, b, v] = node.args;
    const x = polyVar([a, b], v);
    const pa = polyOf(a, x), pb = polyOf(b, x);
    if (!pa.length && !pb.length) throw unsupported("the gcd of two zero polynomials is not defined");
    const g = P.monic(P.gcd(pa, pb));
    const G = P.toTree(g, x);
    return { ...exact(G), verify: () => {
      // independent: g divides both inputs and the cofactors have nonzero resultant (no common root)
      const ra = P.divmod(pa, g), rb = P.divmod(pb, g);
      const divides = !ra.r.length && !rb.r.length;
      const coprime = !ra.q.length || !rb.q.length || degOf(ra.q) === 0 || degOf(rb.q) === 0 || !Nm.isZero(P.resultant(ra.q, rb.q));
      return V(divides && coprime ? "verified-exact" : "failed", "the result divides both polynomials and the cofactors share no root (nonzero resultant)", "gcd-definition");
    } };
  },
  coeff(node) {
    // coeff(p, x^k), coeff(p, k) or coeff(p, x, k)
    const [a, b, c] = node.args;
    let x, k;
    if (c !== undefined) { x = polyVar([a], b); k = simplify(c); }
    else {
      const t = simplify(b);
      if (t.k === "sym") { x = t.name; k = X.ONE; }
      else if (t.k === "pow" && t.args[0].k === "sym") { x = t.args[0].name; k = t.args[1]; }
      else { x = polyVar([a]); k = t; }
    }
    if (!X.isInt(k) || k.v.n < 0n || k.v.n > 1000n) throw unsupported("the power must be a whole number");
    const cs = P.coefficients(a, x);
    if (!cs) throw unsupported(`${toText(a)} is not a polynomial in ${x}`);
    const i = Number(k.v.n);
    const tree = simplify(cs[i] || X.ZERO);
    return { ...exact(tree), verify: () => {
      // independent: rebuilding sum c_i x^i from all extracted coefficients must give the input back
      const back = X.add(...cs.map((ci, j) => X.mul(ci || X.ZERO, X.pow(X.sym(x), X.num(j)))));
      const st = eqv(back, a);
      return V(st === "failed" ? "failed" : st, `sum of the coefficients times powers of ${x} rebuilds the input`, "rebuild");
    } };
  },
  discriminant(node) {
    const [a, v] = node.args;
    const x = polyVar([a], v);
    const p = polyOf(a, x);
    if (degOf(p) < 1) throw unsupported("the discriminant needs a polynomial of degree at least 1");
    const tree = X.num(P.discriminant(p));
    return { ...exact(tree), verify: () => {
      const n = degOf(p);
      if (n === 1) return V("verified-exact", "a linear polynomial has discriminant 1 by convention", "definition");
      if (n === 2) { const [cc, bb, aa] = p.map((t) => Nm.toFloat(t)); return numCheck(bb * bb - 4 * aa * cc, tree, "b^2 - 4ac"); }
      if (n > 8) return { status: "inconclusive", checks: [] };
      // independent: lc^(2n-2) prod_{i<j} (r_i - r_j)^2 over numerical roots (Aberth iteration)
      const roots = [];
      for (const r of P.complexRoots(p)) for (let m = 0; m < r.multiplicity; m++) roots.push(r);
      let re = 1, im = 0;
      for (let i = 0; i < roots.length; i++) for (let j = i + 1; j < roots.length; j++) {
        const dr = roots[i].re - roots[j].re, di = roots[i].im - roots[j].im;
        const sr = dr * dr - di * di, si = 2 * dr * di;
        [re, im] = [re * sr - im * si, re * si + im * sr];
      }
      const lead = Nm.toFloat(p[n]) ** (2 * n - 2);
      const want = re * lead, got = L.evalFloat(tree);
      const ok = Math.abs(want - got) <= 1e-6 * Math.max(1, Math.abs(got)) && Math.abs(im * lead) <= 1e-6 * Math.max(1, Math.abs(got));
      return V(ok ? "verified-numeric" : "failed", `product of squared root differences (${+want.toPrecision(10)}) agrees`, "root-product");
    } };
  },
  circle(node) {
    // x^2 + y^2 + D x + E y + F = 0 (any common leading coefficient): centre and radius
    const [u] = node.args;
    const m = xyCoeffs(u);
    if (!m) throw unsupported("the circle must be a polynomial equation in x and y with number coefficients");
    const A = cf(m, "2,0");
    const allowed = new Set(["2,0", "0,2", "1,0", "0,1", "0,0"]);
    if (Nm.isZero(A) || Nm.cmp(A, cf(m, "0,2")) !== 0 || [...m.keys()].some((k) => !allowed.has(k))) throw unsupported("this is not the equation of a circle (x^2 and y^2 need equal coefficients and there can be no xy term)");
    const D = Nm.div(cf(m, "1,0"), A), E = Nm.div(cf(m, "0,1"), A), F = Nm.div(cf(m, "0,0"), A);
    const h = Nm.div(Nm.neg(D), Nm.TWO), k = Nm.div(Nm.neg(E), Nm.TWO);
    const r2 = Nm.sub(Nm.add(Nm.mul(h, h), Nm.mul(k, k)), F);
    const eq = sideOf(u);
    if (!Nm.isPos(r2)) {
      const label = Nm.isZero(r2) ? `a single point (${Nm.toString(h)}, ${Nm.toString(k)}), radius 0` : "no real points: the radius squared would be negative";
      return { answers: [{ kind: "none", label: `Not a real circle: ${label}.` }], solutionStatus: "exact", verify: () => {
        const v = evalReal(eq, { x: Nm.toFloat(h), y: Nm.toFloat(k) }), a = Nm.toFloat(A);
        // at the centre the left side equals -A r^2, which is >= 0 exactly when there is no real circle
        return V(Number.isFinite(v) && v * Math.sign(a) >= -1e-9 ? "verified-numeric" : "failed", "the left side at the centre has the sign that rules out a real circle", "centre-value");
      } };
    }
    const C = X.tuple(X.num(h), X.num(k)), R = simplify(X.sqrt(X.num(r2)));
    return {
      answers: [{ kind: "exact", tree: C, label: "centre" }, { kind: "exact", tree: R, label: "radius" }], solutionStatus: "exact",
      verify: () => {
        // independent: points on the claimed circle satisfy the equation; points just off it do not
        const hf = Nm.toFloat(h), kf = Nm.toFloat(k), rf = L.evalFloat(R);
        const scale = Math.max(1, Math.abs(Nm.toFloat(A)) * rf * rf);
        const on = [0.3, 1.1, 2.5, 4.0, 5.5].every((t) => Math.abs(evalReal(eq, { x: hf + rf * Math.cos(t), y: kf + rf * Math.sin(t) })) <= 1e-9 * scale);
        const off = [0.7, 3.3].every((t) => Math.abs(evalReal(eq, { x: hf + 1.3 * rf * Math.cos(t), y: kf + 1.3 * rf * Math.sin(t) })) > 1e-6 * scale);
        return V(on && off ? "verified-numeric" : "failed", "points on the claimed circle satisfy the equation and points 30% further out do not", "points");
      },
    };
  },
  linedist(node) {
    // distance from (x0, y0) to the line a x + b y + c = 0
    const [px, py, ln] = node.args;
    const x0 = simplify(px), y0 = simplify(py);
    const m = ln && xyCoeffs(ln);
    if (!m || [...m.keys()].some((k) => !["1,0", "0,1", "0,0"].includes(k))) throw unsupported("the line must be linear in x and y, like 3x + 4y - 5 = 0");
    const a = cf(m, "1,0"), b = cf(m, "0,1"), c = cf(m, "0,0");
    if (Nm.isZero(a) && Nm.isZero(b)) throw unsupported("that is not a line");
    const tree = simplify(X.div(X.fn("abs", X.add(X.mul(X.num(a), x0), X.mul(X.num(b), y0), X.num(c))), X.sqrt(X.num(Nm.add(Nm.mul(a, a), Nm.mul(b, b))))));
    return { ...exact(tree), verify: () => {
      // independent: closest point on the line by ternary search along a parametrisation
      const af = Nm.toFloat(a), bf = Nm.toFloat(b), cf0 = Nm.toFloat(c), X0 = L.evalFloat(x0), Y0 = L.evalFloat(y0);
      const pt = (t) => (Math.abs(bf) > Math.abs(af) ? [t, -(af * t + cf0) / bf] : [-(bf * t + cf0) / af, t]);
      const dist = (t) => { const [x, y] = pt(t); return Math.hypot(x - X0, y - Y0); };
      let lo = -1e6, hi = 1e6;
      for (let i = 0; i < 400; i++) { const m1 = lo + (hi - lo) / 3, m2 = hi - (hi - lo) / 3; if (dist(m1) < dist(m2)) hi = m2; else lo = m1; }
      const want = dist((lo + hi) / 2);
      return V(close(want, L.evalFloat(tree), 1e-7) ? "verified-numeric" : "failed", `the nearest point of the line, found by search, is ${+want.toPrecision(10)} away`, "nearest-point");
    } };
  },
  diffat(node, env) {
    // derivative of f with respect to x, evaluated at x = a
    const [f, xv, a] = node.args;
    if (!xv || xv.k !== "sym" || !a) throw unsupported("diffat(f, x, a)");
    if (X.freeSymbols(a).size || [...X.freeSymbols(f)].some((s) => s !== xv.name)) throw unsupported("the function must depend on one variable and the point must be a number");
    const d = diffFn(f, xv, { order: 1, ctx: env && env.ctx });
    const v = simplify(X.subs(d, { [xv.name]: simplify(a) }));
    if (v === X.UNDEF || X.freeSymbols(v).size) throw unsupported("the derivative does not exist there");
    return { ...exact(v), verify: () => {
      // independent: Richardson-extrapolated central differences of the input
      const af = L.evalFloat(simplify(a)), F = (t) => evalReal(f, { [xv.name]: t });
      const D = (h) => (F(af + h) - F(af - h)) / (2 * h);
      const h = 1e-3 * Math.max(1, Math.abs(af));
      const want = (4 * D(h / 2) - D(h)) / 3, got = L.evalFloat(v);
      if (!Number.isFinite(want)) return { status: "inconclusive", checks: [] };
      return V(Math.abs(want - got) <= 1e-6 * Math.max(1, Math.abs(got)) ? "verified-numeric" : "failed", `central differences at ${+af.toPrecision(10)} give ${+want.toPrecision(10)}`, "finite-difference");
    } };
  },
  dblint(node) {
    // iterated integral: int_c^d int_a^b f dx dy (inner bounds may depend on the outer variable)
    const [f, xv, a, b, yv, c, d] = node.args;
    if (!d || xv.k !== "sym" || yv.k !== "sym") throw unsupported("dblint(f, x, a, b, y, c, d)");
    if (X.freeSymbols(c).size || X.freeSymbols(d).size) throw unsupported("the outer limits must be numbers");
    const inner = definiteIntegral(f, xv, a, b);
    if (inner.status !== "exact") throw unsupported("the inner integral has no exact value");
    const outer = definiteIntegral(inner.value, yv, c, d);
    if (outer.status !== "exact") throw unsupported("the outer integral has no exact value");
    const tree = simplify(outer.value);
    return { ...exact(tree), verify: () => {
      // independent: composite Simpson in both variables on the original integrand
      const cf = L.evalFloat(simplify(c)), df = L.evalFloat(simplify(d)), n = 200;
      const simpson = (g, lo, hi) => { const h = (hi - lo) / n; let t = g(lo) + g(hi); for (let i = 1; i < n; i++) t += (i % 2 ? 4 : 2) * g(lo + i * h); return (t * h) / 3; };
      const want = simpson((yy) => {
        const lo = evalReal(a, { [yv.name]: yy }), hi = evalReal(b, { [yv.name]: yy });
        return simpson((xx) => evalReal(f, { [xv.name]: xx, [yv.name]: yy }), lo, hi);
      }, cf, df);
      if (!Number.isFinite(want)) return { status: "inconclusive", checks: [] };
      return V(Math.abs(want - L.evalFloat(tree)) <= 1e-6 * Math.max(1, Math.abs(want)) ? "verified-numeric" : "failed", `two-dimensional Simpson quadrature gives ${+want.toPrecision(10)}`, "quadrature");
    } };
  },
  grad(node, env) {
    // gradient (partial derivatives) of f with respect to the listed variables
    const [f, ...vs] = node.args;
    if (!vs.length || vs.some((v) => v.k !== "sym")) throw unsupported("grad(f, x, y[, z])");
    const parts = vs.map((v) => simplify(diffFn(f, v, { order: 1, ctx: env && env.ctx })));
    const tree = X.tuple(...parts);
    return { ...exact(tree), verify: () => {
      // independent: central differences in each variable at several random points
      const names = [...new Set([...X.freeSymbols(f), ...vs.map((v) => v.name)])];
      let checked = 0;
      for (const seed of [0.37, 0.81, 1.23, -0.64, 1.7]) {
        const p = Object.fromEntries(names.map((nm, i) => [nm, seed + 0.29 * i]));
        for (let i = 0; i < vs.length; i++) {
          const h = 1e-4, v = vs[i].name;
          const fd = (evalReal(f, { ...p, [v]: p[v] + h }) - evalReal(f, { ...p, [v]: p[v] - h })) / (2 * h);
          const got = evalReal(parts[i], p);
          if (!Number.isFinite(fd) || !Number.isFinite(got)) continue;
          if (Math.abs(fd - got) > 1e-5 * Math.max(1, Math.abs(got))) return V("failed", `component ${i + 1} disagrees with a central difference`, "finite-difference");
          checked++;
        }
      }
      return checked >= 3 * vs.length ? V("verified-numeric", `every component agrees with central differences at ${checked} probes`, "finite-difference") : { status: "inconclusive", checks: [] };
    } };
  },
  solvein(node, env) {
    // solvein(equation, x, a, b, closedLeft, closedRight): the solutions of a one-variable equation
    // that lie in an interval, from the general solution (k integer) or the finite solution list
    const [eq, xv, a, b, cl = X.ONE, cr = X.ONE] = node.args;
    if (!eq || eq.k !== "eq" || xv.k !== "sym" || !b) throw unsupported("solvein(equation, x, a, b)");
    if ([...X.freeSymbols(eq)].some((s) => s !== xv.name)) throw unsupported("the equation must have one variable");
    const lo = L.evalFloat(simplify(a)), hi = L.evalFloat(simplify(b));
    if (!(Number.isFinite(lo) && Number.isFinite(hi) && hi > lo) || hi - lo > 1e4) throw unsupported("the interval must be finite and not too long");
    const closedL = simplify(cl) !== X.ZERO, closedR = simplify(cr) !== X.ZERO;
    const inside = (t) => (closedL ? t >= lo - 1e-12 * Math.max(1, Math.abs(lo)) : t > lo + 1e-12 * Math.max(1, Math.abs(lo))) && (closedR ? t <= hi + 1e-12 * Math.max(1, Math.abs(hi)) : t < hi - 1e-12 * Math.max(1, Math.abs(hi)));
    const r = solveTree(eq, { variable: xv.name, timeLimit: 4000 });
    if (!r.ok || !r.verification || r.verification.status !== "passed") throw unsupported("the equation could not be solved with verification");
    const found = [];
    for (const ans of r.answers || []) {
      if (ans.kind === "exact" && ans.tree) found.push(ans.tree);
      else if (ans.kind === "general" && ans.tree && ans.param) {
        for (let k = -2000; k <= 2000; k++) {
          const t = simplify(X.subs(ans.tree, { [ans.param]: X.num(k) }));
          const v = L.evalFloat(t);
          if (Number.isFinite(v) && inside(v)) found.push(t);
        }
      } else if (ans.kind !== "none") throw unsupported("the solution set has a form that cannot be restricted to an interval");
    }
    const roots = [];
    for (const t of found) { const v = L.evalFloat(t); if (inside(v) && !roots.some((u) => Math.abs(L.evalFloat(u) - v) < 1e-10)) roots.push(t); }
    roots.sort((p, q) => L.evalFloat(p) - L.evalFloat(q));
    const f = X.sub(eq.args[0], eq.args[1]);
    const iv = `${closedL ? "[" : "("}${toText(simplify(a))}, ${toText(simplify(b))}${closedR ? "]" : ")"}`;
    const answers = roots.length ? roots.map((t) => ({ kind: "exact", tree: t, label: xv.name })) : [{ kind: "none", label: `No solutions in ${iv}` }];
    return {
      answers, solutionStatus: "exact", noSolution: !roots.length, note: `Solutions in ${iv}.`,
      verify: () => {
        // independent: each answer satisfies the equation; a fine scan of the interval finds no other root
        const F = (t) => evalReal(f, { [xv.name]: t });
        const vals = roots.map((t) => L.evalFloat(t));
        const scale = Math.max(1, ...Array.from({ length: 50 }, (_, i) => Math.abs(F(lo + ((hi - lo) * (i + 0.5)) / 50))).filter(Number.isFinite));
        if (!vals.every((v) => Math.abs(F(v)) <= 1e-9 * scale && inside(v))) return V("failed", "an answer does not satisfy the equation", "substitute");
        const n = 20000, h = (hi - lo) / n;
        const near = (t) => vals.some((v) => Math.abs(v - t) <= 3 * h);
        let prev = F(lo), prev2 = NaN;
        for (let i = 1; i <= n; i++) {
          const t = lo + i * h, cur = F(t);
          if (Number.isFinite(prev) && Number.isFinite(cur) && prev * cur < 0 && !near(t)) {
            // bracketed sign change: a root unless it is a pole (|f| large on both sides)
            if (Math.min(Math.abs(prev), Math.abs(cur)) < 1e-3 * scale) return V("failed", `the scan found a root near ${+t.toPrecision(8)} that is not in the answer`, "scan");
          }
          if (Number.isFinite(cur) && Math.abs(cur) < 1e-12 * scale && !near(t) && inside(t)) return V("failed", `the scan found a root near ${+t.toPrecision(8)} that is not in the answer`, "scan");
          // a touching (double) root has no sign change: a local minimum of |f| that is nearly zero
          if (Number.isFinite(prev2) && Number.isFinite(cur) && Math.abs(prev) <= Math.abs(prev2) && Math.abs(prev) <= Math.abs(cur) && Math.abs(prev) < 1e-6 * scale && !near(t - h) && inside(t - h))
            return V("failed", `the scan found a possible touching root near ${+(t - h).toPrecision(8)} that is not in the answer`, "scan");
          prev2 = prev;
          prev = cur;
        }
        const endRoots = [[lo, closedL], [hi, closedR]].filter(([t, c]) => c && Math.abs(F(t)) <= 1e-12 * scale && !vals.some((v) => Math.abs(v - t) < 1e-9));
        if (endRoots.length) return V("failed", "an endpoint of the interval is a root that is missing", "endpoints");
        return V("verified-numeric", `every answer satisfies the equation and a ${n}-step scan of ${iv} finds no other sign change`, "scan");
      },
    };
  },
  polar(node) {
    // polar form of a complex number: r = |z|, theta = arg z in (-pi, pi]
    const z = simplify(node.args[0]);
    if (X.freeSymbols(z).size) throw unsupported("polar form needs a number");
    const parts = complexParts(z);
    if (!parts) throw unsupported("could not split the number into real and imaginary parts");
    const a = simplify(parts.re), b = simplify(parts.im), af = L.evalFloat(a), bf = L.evalFloat(b);
    if (!Number.isFinite(af) || !Number.isFinite(bf)) throw unsupported("the parts are not finite numbers");
    if (Math.abs(af) < 1e-12 && Math.abs(bf) < 1e-12) throw unsupported("0 has no argument");
    const r = simplify(X.pow(X.add(X.pow(a, X.num(2)), X.pow(b, X.num(2))), X.HALF));
    let t;
    if (Math.abs(af) < 1e-12) {
      if (equivalent(a, X.ZERO).status !== "equivalent-exact") throw unsupported("cannot decide whether the real part is zero");
      t = simplify(X.mul(X.num(bf > 0 ? 1 : -1), X.PI, X.HALF));
    } else {
      const base = X.fn("atan", X.mul(b, X.pow(a, X.NEG_ONE)));
      t = simplify(af > 0 ? base : X.add(base, X.mul(X.num(bf >= 0 ? 1 : -1), X.PI)));
    }
    const form = simplify(X.mul(r, X.pow(X.E, simplify(X.mul(X.I, t)))));
    return {
      answers: [{ kind: "exact", tree: r, label: "r = |z|" }, { kind: "exact", tree: t, label: "theta = arg z" }, { kind: "exact", tree: form, label: "z" }], solutionStatus: "exact",
      verify: () => {
        // independent: r cos(theta) and r sin(theta) give back the real and imaginary parts
        const zc = evalC(z, {}, "complex"), rf = L.evalFloat(r), tf = L.evalFloat(t);
        const ok = rf >= 0 && tf > -Math.PI - 1e-12 && tf <= Math.PI + 1e-12 && Math.abs(rf * Math.cos(tf) - zc.re) <= 1e-9 * Math.max(1, rf) && Math.abs(rf * Math.sin(tf) - zc.im) <= 1e-9 * Math.max(1, rf);
        return V(ok ? "verified-numeric" : "failed", "r cos(theta) + i r sin(theta) gives back the number", "reconstruct");
      },
    };
  },
  rootsum(node) { return vieta(node, "sum"); },
  rootprod(node) { return vieta(node, "product"); },
  vertex(node) {
    const [a, v] = node.args;
    const x = polyVar([a], v);
    const p = polyOf(a, x);
    if (degOf(p) !== 2) throw unsupported("the vertex needs a quadratic");
    const [c0, b0, a0] = p;
    const h = Nm.div(Nm.neg(b0), Nm.mul(Nm.TWO, a0));
    const k = P.evalAt(p, h);
    const tree = X.tuple(X.num(h), X.num(k));
    return { ...exact(tree, { label: Nm.isPos(a0) ? "vertex (minimum)" : "vertex (maximum)" }), verify: () => {
      // independent: f(h + t) = f(h - t) (symmetry) and f(h) = k, evaluated in floating point on the input
      const f = (t) => evalReal(a, { [x]: t });
      const hf = Nm.toFloat(h), kf = Nm.toFloat(k);
      const ok = close(f(hf), kf) && [0.5, 1.3, 2.7].every((t) => close(f(hf + t), f(hf - t)));
      return V(ok ? "verified-numeric" : "failed", "the parabola is symmetric about the vertex and passes through it", "symmetry");
    } };
  },
};

// Sum / product of all complex roots counted with multiplicity (Vieta), checked on numerical roots.
function vieta(node, what) {
  const [a, v] = node.args;
  const x = polyVar([sideOf(a)], v);
  const p = polyOf(sideOf(a), x);
  const n = degOf(p);
  if (n < 1) throw unsupported("a polynomial of degree at least 1 is needed");
  const val = what === "sum" ? Nm.div(Nm.neg(p[n - 1]), p[n]) : Nm.div(n % 2 ? Nm.neg(p[0]) : p[0], p[n]);
  const tree = X.num(val);
  return { ...exact(tree), note: `Vieta's formulas: the ${what} of all ${n} roots, complex ones included, each counted with its multiplicity.`, verify: () => {
    if (n > 12) return { status: "inconclusive", checks: [] };
    let re = what === "sum" ? 0 : 1, im = 0;
    for (const r of P.complexRoots(p)) for (let k = 0; k < r.multiplicity; k++) {
      if (what === "sum") { re += r.re; im += r.im; } else [re, im] = [re * r.re - im * r.im, re * r.im + im * r.re];
    }
    const got = Nm.toFloat(val);
    const ok = Math.abs(re - got) <= 1e-7 * Math.max(1, Math.abs(got)) && Math.abs(im) <= 1e-7 * Math.max(1, Math.abs(got));
    return V(ok ? "verified-numeric" : "failed", `the ${what} of the numerically computed roots is ${+re.toPrecision(10)}`, "roots");
  } };
}

// ------------------------------------------------------------ matrix arithmetic
// [[1,2],[3,4]] * [[5,6],[7,8]], A^10, A^-1, 2A + B: evaluated exactly with linalg, then checked
// by an independent floating-point evaluation of the input (plain arrays, naive products,
// Gauss-Jordan inverse).
const hasMatrix = (u) => u && (u.k === "matrix" || (u.args || []).some((a) => a && a.k && hasMatrix(a)));
export { hasMatrix };
export function matrixEval(u) {
  if (u.k === "matrix") return { m: L.toMatrix(u) };
  if (!hasMatrix(u)) return { s: simplify(u) };
  if (u.k === "mul") {
    let acc = null, sc = X.ONE;
    for (const a of u.args) {
      const r = matrixEval(a);
      if (r.m) acc = acc ? L.mul(acc, r.m) : r.m; else sc = X.mul(sc, r.s);
    }
    return { m: L.scale(simplify(sc), acc) };
  }
  if (u.k === "add") {
    let acc = null;
    for (const a of u.args) {
      const r = matrixEval(a);
      if (!r.m) throw unsupported("cannot add a number to a matrix");
      acc = acc ? L.add(acc, r.m) : r.m;
    }
    return { m: acc };
  }
  if (u.k === "pow") {
    const b = matrixEval(u.args[0]), e = simplify(u.args[1]);
    if (!b.m || !X.isInt(e)) throw unsupported("a matrix can only be raised to an integer power");
    return { m: L.power(b.m, e) };
  }
  throw unsupported("this operation on matrices is not supported");
}
function fMatrix(u) { // independent float evaluation: returns { m: number[][] } or { s: number }
  if (u.k === "matrix") return { m: u.args.map((r) => (r.args ? r.args : [r]).map((t) => L.evalFloat(simplify(t)))) };
  if (!hasMatrix(u)) return { s: L.evalFloat(simplify(u)) };
  const mm = (A, B) => A.map((r) => B[0].map((_, j) => r.reduce((s, v, k) => s + v * B[k][j], 0)));
  if (u.k === "mul") {
    let acc = null, sc = 1;
    for (const a of u.args) { const r = fMatrix(a); if (r.m) acc = acc ? mm(acc, r.m) : r.m; else sc *= r.s; }
    return { m: acc.map((r) => r.map((v) => v * sc)) };
  }
  if (u.k === "add") {
    const ms = u.args.map((a) => fMatrix(a).m);
    return { m: ms[0].map((r, i) => r.map((_, j) => ms.reduce((s, M) => s + M[i][j], 0))) };
  }
  if (u.k === "pow") {
    let A = fMatrix(u.args[0]).m;
    let k = Number(simplify(u.args[1]).v.n);
    if (Math.abs(k) > 2000) return null;
    if (k < 0) { A = fInverse(A); if (!A) return null; k = -k; }
    let R = A.map((r, i) => r.map((_, j) => (i === j ? 1 : 0)));
    for (let i = 0; i < k; i++) R = mm(R, A);
    return { m: R };
  }
  return null;
}
function fInverse(A) {
  const n = A.length, M = A.map((r, i) => [...r, ...r.map((_, j) => (i === j ? 1 : 0))]);
  for (let c = 0; c < n; c++) {
    let p = c;
    for (let i = c + 1; i < n; i++) if (Math.abs(M[i][c]) > Math.abs(M[p][c])) p = i;
    if (Math.abs(M[p][c]) < 1e-12) return null;
    [M[p], M[c]] = [M[c], M[p]];
    const d = M[c][c];
    for (let j = 0; j < 2 * n; j++) M[c][j] /= d;
    for (let i = 0; i < n; i++) if (i !== c) { const f = M[i][c]; for (let j = 0; j < 2 * n; j++) M[i][j] -= f * M[c][j]; }
  }
  return M.map((r) => r.slice(n));
}
export function matrixCheck(u, R) {
  let f;
  try { f = fMatrix(u); } catch (_) { f = null; }
  if (!f || !f.m) return { status: "inconclusive", checks: [] };
  const got = R.args.map((r) => (r.args ? r.args : [r]).map((t) => L.evalFloat(t)));
  const ok = got.length === f.m.length && got.every((r, i) => r.length === f.m[i].length && r.every((v, j) => close(v, f.m[i][j], 1e-8)));
  return V(ok ? "verified-numeric" : "failed", "independent floating-point matrix arithmetic gives the same entries", "recompute");
}
