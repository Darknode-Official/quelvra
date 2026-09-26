// Quelvra polynomial roots: closed forms (degree <= 4 and binomials), certified real
// approximations, and numerical complex roots (Aberth-Ehrlich, double precision, labelled approximate).

import * as N from "./num.js";
import * as X from "./expr.js";
import { expand, makeCtx } from "./simplify.js";
import * as C from "./poly-core.js";
import { factorQ } from "./poly-factor.js";

const { guard, tick, budgetError, canon } = C;
const S = C.RB; // raw builders; results are canonicalised with canon()
const Q0 = N.ZERO, Q1 = N.ONE;
const num = (r) => X.num(r);
const q = (n, d = 1n) => X.num(N.Q(n, d));

// ---------------------------------------------------------------- numeric evaluation (double complex)
const cx = (re, im = 0) => ({ re, im });
const cadd = (a, b) => cx(a.re + b.re, a.im + b.im);
const cmul = (a, b) => cx(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re);
const cdiv = (a, b) => { const d = b.re * b.re + b.im * b.im; return cx((a.re * b.re + a.im * b.im) / d, (a.im * b.re - a.re * b.im) / d); };
const cabs = (a) => Math.hypot(a.re, a.im);
function cpowReal(a, e) { // principal power
  if (a.re === 0 && a.im === 0) return e > 0 ? cx(0) : cx(NaN);
  const r = Math.pow(cabs(a), e), t = Math.atan2(a.im, a.re) * e;
  return cx(r * Math.cos(t), r * Math.sin(t));
}
// Evaluate a constant tree numerically with the engine's real-domain conventions
// (odd roots of negative reals are real). Returns { re, im } or null.
export function evalComplex(u) {
  const go = (w) => {
    switch (w.k) {
      case "num": return cx(N.toFloat(w.v));
      case "const":
        if (w.name === "pi") return cx(Math.PI);
        if (w.name === "e") return cx(Math.E);
        if (w.name === "I") return cx(0, 1);
        return null;
      case "add": { let s = cx(0); for (const a of w.args) { const v = go(a); if (!v) return null; s = cadd(s, v); } return s; }
      case "mul": { let s = cx(1); for (const a of w.args) { const v = go(a); if (!v) return null; s = cmul(s, v); } return s; }
      case "pow": {
        const b = go(w.args[0]);
        const e = w.args[1];
        if (!b) return null;
        if (X.isNum(e)) {
          const { n, d } = e.v;
          if (d === 1n) {
            let k = Number(n < 0n ? -n : n), r = cx(1), base = b;
            while (k) { if (k & 1) r = cmul(r, base); k >>= 1; if (k) base = cmul(base, base); }
            return n < 0n ? cdiv(cx(1), r) : r;
          }
          if (Math.abs(b.im) === 0 && b.re < 0 && d % 2n === 1n) {
            const m = Math.pow(-b.re, Number(n) / Number(d));
            return cx(n % 2n === 0n ? m : -m);
          }
          return cpowReal(b, Number(n) / Number(d));
        }
        const ev = go(e);
        if (!ev) return null;
        if (w.args[0] === X.E) { const m = Math.exp(ev.re); return cx(m * Math.cos(ev.im), m * Math.sin(ev.im)); }
        if (ev.im === 0) return cpowReal(b, ev.re);
        return null;
      }
      case "fn": {
        const a = w.args.map(go);
        if (a.some((v) => !v)) return null;
        const r = a[0];
        const real = r && Math.abs(r.im) <= 1e-300;
        switch (w.name) {
          case "cos": return real ? cx(Math.cos(r.re)) : null;
          case "sin": return real ? cx(Math.sin(r.re)) : null;
          case "tan": return real ? cx(Math.tan(r.re)) : null;
          case "acos": return real && Math.abs(r.re) <= 1 ? cx(Math.acos(r.re)) : null;
          case "asin": return real && Math.abs(r.re) <= 1 ? cx(Math.asin(r.re)) : null;
          case "atan": return real ? cx(Math.atan(r.re)) : null;
          case "abs": return cx(cabs(r));
          case "sqrt": return real && r.re < 0 ? cx(0, Math.sqrt(-r.re)) : cpowReal(r, 0.5);
          case "cbrt": return real ? cx(Math.cbrt(r.re)) : cpowReal(r, 1 / 3);
          case "ln": return real && r.re > 0 ? cx(Math.log(r.re)) : null;
          case "exp": return real ? cx(Math.exp(r.re)) : null;
          default: return null;
        }
      }
      default: return null;
    }
  };
  return go(u);
}
function hornerC(p, z) {
  // p: array of numbers (low -> high); returns value and scale sum |a_i||z|^i
  let v = cx(0), s = 0;
  const az = cabs(z);
  for (let i = p.length - 1; i >= 0; i--) { v = cadd(cmul(v, z), cx(p[i])); s = s * az + Math.abs(p[i]); }
  return { v, s };
}
function floatCoeffs(p) {
  // scale integer coefficients to avoid overflow in toFloat
  const z = C.toZ(p).z;
  let maxBits = 0;
  for (const c of z) maxBits = Math.max(maxBits, (c < 0n ? -c : c).toString(2).length);
  const shift = BigInt(Math.max(0, maxBits - 900));
  return z.map((c) => Number(c >> shift) || (c === 0n ? 0 : Number(c) / 2 ** Number(shift)));
}

// ---------------------------------------------------------------- Aberth-Ehrlich
function aberth(p, maxIter = 600) {
  const a = floatCoeffs(p);
  const n = a.length - 1;
  if (n < 1) return [];
  const lcf = a[n];
  const m = a.map((v) => v / lcf);
  if (n === 1) return [{ z: cx(-m[0]), residual: 0, converged: true, iterations: 0 }];
  let R = 0;
  for (let i = 0; i < n; i++) R = Math.max(R, Math.pow(Math.abs(m[i]), 1 / (n - i)));
  R = Math.max(R, 1e-3);
  const zs = [];
  for (let k = 0; k < n; k++) { const t = (2 * Math.PI * k) / n + 0.4; zs.push(cx(R * Math.cos(t), R * Math.sin(t))); }
  const dm = m.slice(1).map((v, i) => v * (i + 1));
  let it = 0, converged = false;
  for (; it < maxIter; it++) {
    tick(n);
    let maxStep = 0;
    for (let k = 0; k < n; k++) {
      const z = zs[k];
      const pv = hornerC(m, z).v, dv = hornerC(dm, z).v;
      if (cabs(pv) === 0) continue;
      const ratio = cdiv(pv, dv);
      let sum = cx(0);
      for (let j = 0; j < n; j++) if (j !== k) sum = cadd(sum, cdiv(cx(1), cadd(z, cx(-zs[j].re, -zs[j].im))));
      const denom = cadd(cx(1), cx(-(ratio.re * sum.re - ratio.im * sum.im), -(ratio.re * sum.im + ratio.im * sum.re)));
      const w = cdiv(ratio, denom);
      if (!isFinite(w.re) || !isFinite(w.im)) continue;
      zs[k] = cadd(z, cx(-w.re, -w.im));
      maxStep = Math.max(maxStep, cabs(w) / Math.max(1, cabs(zs[k])));
    }
    if (maxStep < 1e-15) { converged = true; break; }
  }
  return zs.map((z) => {
    const { v, s } = hornerC(m, z);
    return { z, residual: s > 0 ? cabs(v) / s : cabs(v), converged, iterations: it };
  });
}
const approxRec = (x, method, it, conv) => ({ value: fmt(x), digits: 15, requested: 15, errorBound: null, method, iterations: it, converged: conv });
function fmt(x) { if (Object.is(x, -0) || Math.abs(x) < 1e-300) return "0"; return String(Number(x.toPrecision(15))); }

// All complex roots numerically: [{ re, im, multiplicity, residual, approx: {re, im} }].
// Square-free parts are solved separately so repeated roots are reported with multiplicity.
export function complexRoots(p, opts) {
  return guard(opts, () => {
    p = C.norm(p);
    if (!p.length) throw new RangeError("Quelvra: the zero polynomial has infinitely many roots");
    const out = [];
    for (const { poly: f, mult } of C.squareFree(p).factors) {
      for (const r of aberth(f)) {
        const re = Math.abs(r.z.im) <= 1e-14 * Math.max(1, cabs(r.z)) ? r.z.re : r.z.re;
        const im = Math.abs(r.z.im) <= 1e-14 * Math.max(1, cabs(r.z)) ? 0 : r.z.im;
        out.push({ re, im, multiplicity: mult, residual: r.residual, approx: { re: approxRec(re, "aberth", r.iterations, r.converged), im: approxRec(im, "aberth", r.iterations, r.converged) } });
      }
    }
    return out.sort((a, b) => a.re - b.re || a.im - b.im);
  });
}

// ---------------------------------------------------------------- closed forms
const R = (r) => num(r);
// Square root of a CONSTANT tree that never produces pow(k*u, 1/2) with k < 0 and u symbolic:
// simplify.js recurses forever on such nodes (foundation bug). A radicand that canonicalises to a
// product with a negative numeric coefficient is rewritten as I*sqrt(-t) when it is numerically a
// negative real; otherwise the construction is abandoned (caller falls back to approximations).
function unsafe() { return Object.assign(new Error("unsafe radical"), { code: "UNSAFE" }); }
function sqrtT(t) {
  if (X.isNum(t)) return S.sqrt(t);
  const c = canon(t);
  if (X.isNum(c)) return S.sqrt(c);
  if (c.k === "mul" && X.isNum(c.args[0]) && N.isNeg(c.args[0].v)) {
    const z = evalComplex(c);
    if (z && Math.abs(z.im) <= 1e-12 * Math.max(1, Math.abs(z.re)) && z.re < 0) return S.mul(X.I, S.sqrt(canon(S.neg(c))));
    throw unsafe();
  }
  return S.sqrt(c);
}
const ratSqrt = (r) => {
  if (N.isNeg(r)) return null;
  const [a, ea] = N.iroot(r.n, 2), [b, eb] = N.iroot(r.d, 2);
  return ea && eb ? N.Q(a, b) : null;
};
const cbrtT = (t) => S.pow(t, q(1n, 3n));
// roots of an irreducible quadratic a x^2 + b x + c (coefficients Rationals)
function quadRoots(c0, c1, c2) {
  const D = N.sub(N.mul(c1, c1), N.mul(N.mul(N.Q(4), c2), c0));
  const sd = sqrtT(R(D));
  const den = R(N.mul(N.TWO, c2));
  const mb = R(N.neg(c1));
  return [
    { root: S.div(S.sub(mb, sd), den), real: !N.isNeg(D) },
    { root: S.div(S.add(mb, sd), den), real: !N.isNeg(D) },
  ];
}
// roots of an irreducible cubic; also used for resolvents. Returns [{root, real}]
function cubicRoots(c) {
  const [d, cc, b, a] = c;
  const shift = N.div(b, N.mul(N.Q(3), a)); // x = t - shift
  const p = N.div(N.sub(N.mul(N.mul(N.Q(3), a), cc), N.mul(b, b)), N.mul(N.Q(3), N.mul(a, a)));
  const qq = N.div(N.add(N.sub(N.mul(N.TWO, N.pow(b, 3)), N.mul(N.mul(N.Q(9), a), N.mul(b, cc))), N.mul(N.mul(N.Q(27), N.mul(a, a)), d)), N.mul(N.Q(27), N.pow(a, 3)));
  const disc = N.sub(N.mul(N.Q(-4), N.pow(p, 3)), N.mul(N.Q(27), N.mul(qq, qq)));
  const sh = R(N.neg(shift));
  if (N.isPos(disc)) {
    // casus irreducibilis: three real roots, trigonometric form
    const amp = S.mul(q(2n), sqrtT(R(N.div(N.neg(p), N.Q(3)))));
    const arg = S.mul(R(N.div(N.mul(N.Q(3), qq), N.mul(N.TWO, p))), sqrtT(R(N.div(N.Q(-3), p))));
    const theta = S.mul(q(1n, 3n), S.fn("acos", arg));
    return [0, 1, 2].map((k) => ({
      root: S.add(S.mul(amp, S.fn("cos", S.sub(theta, S.mul(q(2n * BigInt(k), 3n), X.PI)))), sh), real: true, form: "trigonometric",
    }));
  }
  // one real root (Cardano); disc < 0 (disc = 0 impossible for square-free)
  const D = N.add(N.div(N.mul(qq, qq), N.Q(4)), N.div(N.pow(p, 3), N.Q(27)));
  const h = R(N.div(N.neg(qq), N.TWO));
  const sD = sqrtT(R(D));
  const u = cbrtT(S.add(h, sD)), v = cbrtT(S.sub(h, sD));
  const real = S.add(S.add(u, v), sh);
  const re = S.add(S.mul(q(-1n, 2n), S.add(u, v)), sh);
  const im = S.mul(S.div(sqrtT(q(3n)), q(2n)), S.sub(u, v));
  return [
    { root: real, real: true, form: "cardano" },
    { root: S.sub(re, S.mul(X.I, im)), real: false, form: "cardano" },
    { root: S.add(re, S.mul(X.I, im)), real: false, form: "cardano" },
  ];
}
// roots of an irreducible quartic
function quarticRoots(c) {
  const a = c[4];
  const [E, D, Cc, B] = [0, 1, 2, 3].map((i) => N.div(c[i], a));
  const p = N.sub(Cc, N.div(N.mul(N.Q(3), N.mul(B, B)), N.Q(8)));
  const qq = N.add(N.sub(D, N.div(N.mul(B, Cc), N.TWO)), N.div(N.pow(B, 3), N.Q(8)));
  const r = N.add(N.sub(N.add(N.sub(E, N.div(N.mul(B, D), N.Q(4))), N.div(N.mul(N.mul(B, B), Cc), N.Q(16))), N.div(N.mul(N.Q(3), N.pow(B, 4)), N.Q(256))), Q0);
  const sh = R(N.neg(N.div(B, N.Q(4))));
  const out = [];
  if (qq.n === 0n) {
    // biquadratic: y^2 = alpha +- sqrt(Dq)/2 with alpha = -p/2, Dq = p^2 - 4r
    const Dq = N.sub(N.mul(p, p), N.mul(N.Q(4), r));
    const alpha = N.div(N.neg(p), N.TWO);
    const ys = [];
    if (N.isNeg(Dq)) {
      // y^2 = alpha +- i beta: principal sqrt = sqrt((|z| + alpha)/2) +- i sqrt((|z| - alpha)/2), |z| = sqrt(r)
      const mod = S.sqrt(R(r));
      const re = sqrtT(S.div(S.add(mod, R(alpha)), q(2n))), im = sqrtT(S.div(S.sub(mod, R(alpha)), q(2n)));
      ys.push(S.add(re, S.mul(X.I, im)), S.sub(re, S.mul(X.I, im)));
    } else {
      const sd = S.sqrt(R(Dq));
      const s0 = ratSqrt(r);
      for (const sg of [-1, 1]) {
        // denest sqrt(alpha + sg*sqrt(Dq)/2) when r is a rational square and both parts are real
        if (s0 && !N.isNeg(N.sub(alpha, s0))) {
          const A = N.div(N.add(alpha, s0), N.TWO), B = N.div(N.sub(alpha, s0), N.TWO);
          ys.push(sg > 0 ? S.add(S.sqrt(R(A)), S.sqrt(R(B))) : S.sub(S.sqrt(R(A)), S.sqrt(R(B))));
        } else {
          ys.push(sqrtT(S.add(R(alpha), S.mul(q(BigInt(sg), 2n), sd))));
        }
      }
    }
    for (const y of ys) out.push({ root: S.add(S.neg(y), sh), form: "biquadratic" }, { root: S.add(y, sh), form: "biquadratic" });
    return out;
  }
  // Ferrari: resolvent 8m^3 + 8p m^2 + (2p^2 - 8r) m - q^2 = 0, need m > 0
  const res = [N.neg(N.mul(qq, qq)), N.sub(N.mul(N.TWO, N.mul(p, p)), N.mul(N.Q(8), r)), N.mul(N.Q(8), p), N.Q(8)];
  let mTree = null;
  const rr = C.rationalRoots(res).filter((x) => N.isPos(x));
  if (rr.length) mTree = R(rr[rr.length - 1]);
  else {
    // resolvent irreducible over Q (no rational root) -> cubic formula; choose the largest real root
    const roots = cubicRoots(C.norm(res)).filter((x) => x.real);
    let best = null, bv = -Infinity;
    for (const x of roots) { const v = evalComplex(x.root); if (v && v.re > bv) { bv = v.re; best = x.root; } }
    if (!best || !(bv > 0)) return null;
    mTree = best;
  }
  const s2m = sqrtT(S.mul(q(2n), mTree));
  for (const s of [-1, 1]) {
    const sT = q(BigInt(s));
    const disc = S.sub(S.sub(S.mul(q(-2n), mTree), R(N.mul(N.TWO, p))), S.mul(sT, S.div(R(N.mul(N.TWO, qq)), s2m)));
    const sd = sqrtT(disc);
    for (const t of [-1, 1]) {
      out.push({ root: S.add(S.div(S.add(S.mul(sT, s2m), S.mul(q(BigInt(t)), sd)), q(2n)), sh), form: "ferrari" });
    }
  }
  return out;
}
// x^n = c roots for an irreducible binomial a x^n + b
function binomialRoots(f) {
  const n = f.length - 1;
  const c = N.div(N.neg(f[0]), f[n]);
  const mag = S.pow(R(N.abs(c)), q(1n, BigInt(n)));
  const out = [];
  for (let k = 0; k < n; k++) {
    // angle = (2 pi k + arg c) / n, arg c = 0 or pi
    const num2 = N.isNeg(c) ? 2 * k + 1 : 2 * k; // angle = num2 * pi / n
    const ang = S.mul(q(BigInt(num2), BigInt(n)), X.PI);
    const realRoot = (num2 * 2) % (2 * n) === 0 || num2 === n;
    if (realRoot) out.push({ root: num2 === n ? S.neg(mag) : mag, real: true, form: "binomial" });
    else out.push({ root: S.mul(mag, S.add(S.fn("cos", ang), S.mul(X.I, S.fn("sin", ang)))), real: false, form: "binomial" });
  }
  return out;
}

// ---------------------------------------------------------------- verification
function onlySquareRoots(u) {
  if (u.k === "fn") return false;
  if (u.k === "pow" && X.isNum(u.args[1]) && u.args[1].v.d !== 1n && u.args[1].v.d !== 2n) return false;
  return u.args.every(onlySquareRoots);
}
function verifyExact(root, factorTreeX, x) {
  try {
    const v = expand(X.subs(factorTreeX, { [x]: root }), makeCtx());
    return X.isZero(canon(v));
  } catch (e) {
    if (e && (e.code === "BUDGET" || e instanceof RangeError)) return false;
    throw e;
  }
}
function verifyNumeric(root, fz) {
  const z = evalComplex(root);
  if (!z || !isFinite(z.re) || !isFinite(z.im)) return { ok: false };
  const a = floatCoeffs(C.fromZ(fz));
  const { v, s } = hornerC(a, z);
  const res = s > 0 ? cabs(v) / s : cabs(v);
  return { ok: res < 1e-9, residual: res, z };
}

// Solve p(x) = 0 for a polynomial expression. domain "real" (default) or "complex".
// Returns { exact: [{root, multiplicity, verified: "exact"|"numeric", real}],
//           approx: [{ re, im?, multiplicity, interval? }], complete, conditions, degree }.
export function solvePolynomial(node, x, opts = {}) {
  return guard(opts, () => {
    const domain = opts.domain || "real";
    const xn = typeof x === "string" ? x : x.name;
    const coeffs = C.coefficients(node, xn);
    if (coeffs === null) return { exact: [], approx: [], complete: false, conditions: [], reason: "not a polynomial in " + xn };
    if (!coeffs.every(X.isNum)) return solveSymbolic(coeffs, xn);
    const p = C.norm(coeffs.map((t) => t.v));
    if (!p.length) return { exact: [], approx: [], complete: true, identity: true, conditions: [], degree: -1 };
    if (p.length === 1) return { exact: [], approx: [], complete: true, conditions: [], degree: 0 };
    const fq = factorQ(p);
    const exact = [], approx = [];
    let complete = true;
    for (const { poly: f, mult } of fq.factors) {
      const d = f.length - 1;
      const fz = C.toZ(f).z;
      const ftree = C.toTree(f, xn);
      if (d === 1) {
        exact.push({ root: R(N.div(N.neg(f[0]), f[1])), multiplicity: mult, verified: "exact", real: true });
        continue;
      }
      let cands = null;
      const isBinomial = f.slice(1, d).every((c) => c.n === 0n);
      try {
        if (d === 2) cands = quadRoots(f[0], f[1], f[2]);
        else if (d === 3) cands = cubicRoots(f);
        else if (d === 4) cands = quarticRoots(f);
        else if (isBinomial) cands = binomialRoots(f);
        if (cands) cands = cands.map((c) => ({ ...c, root: canon(c.root) }));
      } catch (e) {
        if (!(e instanceof RangeError) && e.code !== "UNSAFE" && e.code !== "BUDGET") throw e;
        cands = null;
      }
      let ok = !!cands && cands.length === d;
      const nReal = C.countRealRoots(f);
      const accepted = [];
      if (ok) {
        const realIv = C.isolateRealRoots(f).map((iv) => C.refineInterval(f, iv, N.Q(1n, 10n ** 9n)));
        const usedIv = new Set();
        for (const cnd of cands) {
          let verified = null;
          const ex = onlySquareRoots(cnd.root) && verifyExact(cnd.root, ftree, xn);
          const nm = verifyNumeric(cnd.root, fz);
          if (ex) verified = "exact";
          else if (nm.ok) verified = "numeric";
          if (!verified || !nm.z) { ok = false; break; }
          const scaleZ = Math.max(1, cabs(nm.z));
          let isReal = Math.abs(nm.z.im) <= 1e-9 * scaleZ;
          if (isReal) {
            // certify: the value must fall into its own isolating interval of a real root
            const idx = realIv.findIndex((iv, i) => !usedIv.has(i) && nm.z.re >= N.toFloat(iv.lo) - 1e-7 * scaleZ && nm.z.re <= N.toFloat(iv.hi) + 1e-7 * scaleZ);
            if (idx < 0) isReal = false; else usedIv.add(idx);
          }
          accepted.push({ root: cnd.root, multiplicity: mult, verified, real: isReal, form: cnd.form, value: nm.z });
        }
        if (ok && accepted.filter((a) => a.real).length !== nReal) ok = false;
        // distinctness of numeric values
        if (ok) for (let i = 0; i < accepted.length; i++) for (let j = i + 1; j < accepted.length; j++)
          if (cabs(cadd(accepted[i].value, cx(-accepted[j].value.re, -accepted[j].value.im))) < 1e-9 * Math.max(1, cabs(accepted[i].value))) ok = false;
      }
      if (ok) {
        for (const a of accepted) if (domain === "complex" || a.real) exact.push({ root: a.root, multiplicity: a.multiplicity, verified: a.verified, real: a.real, form: a.form });
        continue;
      }
      complete = false;
      // approximations: certified real roots, Aberth for complex ones
      for (const iv of C.isolateRealRoots(f)) approx.push({ re: C.approxRealRoot(f, iv, 20), im: null, multiplicity: mult, interval: [iv.lo, iv.hi], certified: true });
      if (domain === "complex") {
        for (const r of complexRoots(f)) if (r.im !== 0) approx.push({ re: r.approx.re, im: r.approx.im, multiplicity: mult, residual: r.residual, certified: false });
      }
    }
    const val = (t) => { const z = evalComplex(t); return z ? z : cx(NaN); };
    exact.sort((a, b) => (a.real === b.real ? 0 : a.real ? -1 : 1) || val(a.root).re - val(b.root).re || val(a.root).im - val(b.root).im);
    return { exact, approx, complete, conditions: [], degree: p.length - 1 };
  });
}
function solveSymbolic(coeffs, xn) {
  const d = coeffs.length - 1;
  if (d === 1) {
    const [b, a] = coeffs;
    return { exact: [{ root: canon(S.neg(S.div(b, a))), multiplicity: 1, verified: "exact", real: null }], approx: [], complete: true, conditions: [X.rel("!=", a, X.ZERO)], degree: 1, symbolic: true };
  }
  if (d === 2) {
    const [c, b, a] = coeffs;
    const D = canon(S.sub(S.pow(b, q(2n)), S.mul(q(4n), a, c)));
    if (D.k === "mul" && X.isNum(D.args[0]) && N.isNeg(D.args[0].v))
      return { exact: [], approx: [], complete: false, conditions: [], degree: 2, reason: "discriminant is a negative multiple of a product; not representable safely" };
    const sd = S.sqrt(D), den = S.mul(q(2n), a);
    const roots = [S.div(S.sub(S.neg(b), sd), den), S.div(S.add(S.neg(b), sd), den)].map(canon);
    const poly = canon(S.add(...coeffs.map((t, i) => S.mul(t, S.pow(X.sym(xn), q(BigInt(i)))))));
    return {
      exact: roots.map((r) => ({ root: r, multiplicity: 1, verified: verifyExact(r, poly, xn) ? "exact" : "unverified", real: null })),
      approx: [], complete: true, conditions: [X.rel("!=", a, X.ZERO)], degree: 2, symbolic: true,
    };
  }
  return { exact: [], approx: [], complete: false, conditions: [], degree: d, reason: "symbolic coefficients of degree > 2" };
}
// Exact closed-form roots (all complex roots) of a UPoly, or null when some factor has degree > 4.
export function closedFormRoots(p, x = "x") {
  const r = solvePolynomial(C.toTree(p, x), x, { domain: "complex" });
  return r.complete ? r.exact : null;
}
