// Complex analysis: residues (poles of any order), Laurent series (first terms), contour integrals
// over circles by the residue theorem, real integrals over the line by residues, and the
// Cauchy-Riemann analyticity test.
//
// Solver: f = g/h; the pole order m at z0 is the order of the zero of h; the Laurent coefficients
// come from the Taylor coefficients of g and h at z0 (exact derivatives, series division), so
// complex centres such as z0 = i work. Poles are the zeros of a polynomial h from the equation
// solver (complex domain).
// Verifier (independent): contour integrals by the trapezoid rule on circles (at two radii),
// Gauss-Legendre / tanh-sinh quadrature on the real line, and complex difference quotients of the
// ORIGINAL f in several directions.

import { solve as orchestrate } from "../orchestrate.js";
import * as P from "../poly-core.js";
import { oscIntegral } from "./transforms.js";
import {
  X, toText, TCV, fail, safe, pass, bad, open, fmt, fmtC, C, D, nice, tidyTrig, isZeroExact, expand, together, numerDenom,
  valueAnswers, evalR, evalZ, forEval, quadRealLine, numOf, cnumOf, sortVars,
} from "./util.js";
import { makeCtx } from "../simplify.js";

const ctx = () => makeCtx({ budget: { ops: 600000 } });
const S = X.sym;
const hasI = (u) => X.contains(u, X.I);
// functions the verifier's complex evaluator lacks, rewritten through exp / sin / cos
function forEvalC(u) {
  return forEval(X.mapTree(u, (w) => {
    if (w.k !== "fn" || w.args.length !== 1) return w;
    const a = w.args[0];
    if (w.name === "cot") return X.div(X.fn("cos", a), X.fn("sin", a));
    if (w.name === "sec") return X.recip(X.fn("cos", a));
    if (w.name === "csc") return X.recip(X.fn("sin", a));
    if (w.name === "sinh") return X.div(X.sub(X.exp(a), X.exp(X.neg(a))), X.TWO);
    if (w.name === "cosh") return X.div(X.add(X.exp(a), X.exp(X.neg(a))), X.TWO);
    if (w.name === "tanh") return X.div(X.sub(X.exp(a), X.exp(X.neg(a))), X.add(X.exp(a), X.exp(X.neg(a))));
    return w;
  }));
}
const cfn = (u, z) => { const g = forEvalC(u); return (re, im) => evalZ(g, { [z]: { re, im } }); };
const cmulN = (a, b) => ({ re: a.re * b.re - a.im * b.im, im: a.re * b.im + a.im * b.re });
const cabsN = (a) => Math.hypot(a.re, a.im);

// ------------------------------------------------------------------ exact Laurent machinery
function splitGH(f) {
  const [g, h] = numerDenom(C(together(C(f), ctx())));
  return { g: C(g), h: C(h) };
}
// Taylor coefficients u^(k)(z0)/k!, k < K
function taylor(u, z, z0, K) {
  const out = [];
  let d = u, fact = 1n;
  for (let k = 0; k < K; k++) {
    if (k > 0) { d = C(D(d, z)); fact *= BigInt(k); }
    const v = C(X.subs(d, { [z]: z0 }));
    if (v === X.UNDEF || X.contains(v, X.UNDEF)) return null;
    out.push(C(X.div(v, X.num(fact))));
  }
  return out;
}
// zero test: exact identity, or "clearly nonzero" from a numeric value at probe points
function isZ(u) {
  const e = isZeroExact(u);
  if (e !== null) return e;
  const names = [...X.freeSymbols(u)];
  const g = forEvalC(u);
  for (const p of [[0.731, -0.418], [1.327, 0.911], [-0.553, 1.219]]) {
    const env = {}; names.forEach((n, i) => { env[n] = p[i % 2] + 0.1 * i; });
    const v = evalZ(g, env);
    if (v && Number.isFinite(v.re) && Number.isFinite(v.im) && Math.hypot(v.re, v.im) > 1e-8) return false;
  }
  return null;
}
// { m (pole order, <= 0 when analytic), coeffs c_{-m}.. } with K terms after the leading one
function laurentAt(f, z, z0, K) {
  const { g, h } = splitGH(f);
  const maxOrd = 12;
  const hc = taylor(h, z, z0, maxOrd + K + 1);
  if (!hc) throw fail("could not expand the denominator at the point");
  let m = 0;
  while (m < hc.length && isZ(hc[m]) === true) m++;
  if (m >= maxOrd) throw fail("the pole order is too high (or the denominator vanishes identically)");
  if (isZ(hc[m]) !== false) throw fail("could not decide the order of the pole");
  const gc = taylor(g, z, z0, m + K);
  if (!gc) throw fail("could not expand the numerator at the point");
  // G/H with H_j = h_{m + j}
  const H = hc.slice(m, m + m + K);
  const q = [];
  for (let k = 0; k < m + K; k++) {
    let acc = gc[k] || X.ZERO;
    for (let j = 1; j <= k; j++) acc = X.sub(acc, X.mul(H[j] || X.ZERO, q[k - j]));
    q.push(C(X.div(acc, H[0])));
  }
  // f = sum q_k (z - z0)^(k - m)
  return { m, coeffs: q.map((c) => nice(C(c))) };
}
function residueExact(f, z, z0) {
  const { m, coeffs } = laurentAt(f, z, z0, 1);
  if (m <= 0) return { m, value: X.ZERO };
  return { m, value: coeffs[m - 1] };
}
// numeric (1/(2 pi i)) contour integral of f(z) (z - z0)^(-k-1) on |z - z0| = rho
function contourCoef(fz, z0, rho, k, Npts = 512) {
  let sr = 0, si = 0;
  for (let j = 0; j < Npts; j++) {
    const th = (2 * Math.PI * j) / Npts;
    const w = { re: rho * Math.cos(th), im: rho * Math.sin(th) };
    const v = fz(z0.re + w.re, z0.im + w.im);
    if (!v || !Number.isFinite(v.re) || !Number.isFinite(v.im)) return null;
    // f * w^(-k) / N  (since dz = i w dtheta, 1/(2 pi i) * i w * w^(-k-1) = w^(-k)/(2 pi))
    const r = Math.pow(rho, -k), a = -k * th;
    const wk = { re: r * Math.cos(a), im: r * Math.sin(a) };
    const p = cmulN(v, wk);
    sr += p.re; si += p.im;
  }
  return { re: sr / Npts, im: si / Npts };
}
function checkCoef(fz, z0n, k, claimed, what) {
  const a = contourCoef(fz, z0n, 0.05, k), b = contourCoef(fz, z0n, 0.02, k, 1024);
  if (!a || !b) return open("contour", `f could not be evaluated near the point`);
  const want = cnumOf(claimed);
  if (!want) return open("contour", "the value could not be evaluated");
  const sc = Math.max(1, cabsN(want));
  const agree = cabsN({ re: a.re - b.re, im: a.im - b.im }) < 1e-8 * sc;
  if (!agree) return open("contour", "the contour integrals at two radii disagree (another singularity is too close)");
  return cabsN({ re: a.re - want.re, im: a.im - want.im }) < 1e-8 * sc ? pass("contour", `(1/(2 pi i)) times the contour integral on circles of radius 0.05 and 0.02 gives ${fmtC(a)} for the ${what}`) : bad("contour", `the contour integral gives ${fmtC(a)} for the ${what}, not ${fmtC(want)}`);
}
function varOf(node, i, dflt = "z") {
  const a = node.args[i];
  if (a && a.k === "sym") return a.name;
  const f = node.args[0];
  const fs = f ? [...X.freeSymbols(f)] : [];
  return fs.length === 1 ? fs[0] : dflt;
}
// zeros of the polynomial denominator h (complex)
function polesOf(f, z) {
  const { h } = splitGH(f);
  const hp = P.fromTree(C(expand(h, ctx())), z);
  if (!hp) throw fail("finding all poles needs a polynomial denominator");
  if (hp.length <= 1) return [];
  const r = orchestrate(X.eq(C(expand(h, ctx())), X.ZERO), { domain: "complex", variable: z, timeLimit: 6000, crossCheck: false });
  if (!r.ok || !r.verification || r.verification.status !== "passed") throw fail("could not find the poles exactly");
  const pts = [];
  for (const a of r.answers) {
    if (a.kind !== "exact" || !a.tree) throw fail("could not list the poles exactly");
    const v = cnumOf(a.tree);
    if (!v) throw fail("could not evaluate a pole");
    if (!pts.some((p) => cabsN({ re: p.v.re - v.re, im: p.v.im - v.im }) < 1e-12)) pts.push({ tree: C(a.tree), v });
  }
  return pts;
}

// ------------------------------------------------------------------ commands
function cmdResidue(node, env) {
  const f = node.args[0];
  if (!f || ["eq", "vector", "tuple", "matrix"].includes(f.k)) throw fail("residue(f, z, z0)");
  const z = varOf(node, 1);
  const extra = [...X.freeSymbols(f)].filter((v) => v !== z);
  if (extra.length) throw fail(`the function has symbols other than ${z}`);
  const fz = cfn(f, z);
  if (node.args.length >= 3) {
    const z0 = C(node.args[2]);
    if (X.freeSymbols(z0).size) throw fail("the point must be a number");
    const z0n = cnumOf(z0);
    if (!z0n) throw fail("the point is not a finite number");
    const { m, value } = residueExact(f, z, z0);
    const v = tidyTrig(value);
    env.log.add({ rule: "complex.residue", title: m > 0 ? `Pole of order ${m}` : "No pole", why: m > 0 ? `The denominator has a zero of order ${m} at z = ${toText(z0)}; the residue is the coefficient of 1/(z - z0) in the Laurent series.` : "f is analytic (or has a removable singularity) there, so the residue is 0.", before: f, after: v });
    return { answers: [{ kind: "exact", label: `Residue at ${z} = ${toText(z0)}`, tree: v, at: z0 }], verify: () => TCV([checkCoef(fz, z0n, -1, v, "residue")]) };
  }
  const poles = polesOf(f, z);
  if (!poles.length) throw fail("f has no poles (its denominator has no zeros)");
  const res = [];
  for (const p of poles) {
    const { m, value } = residueExact(f, z, p.tree);
    if (m <= 0) continue;
    res.push({ p, v: tidyTrig(value), m });
  }
  if (!res.length) throw fail("every zero of the denominator is a removable singularity");
  env.log.add({ rule: "complex.residues", title: "Residues at all poles", why: `The poles are the zeros of the denominator: ${res.map((r) => `${toText(r.p.tree)} (order ${r.m})`).join(", ")}.`, before: f, after: null, kind: "note" });
  return {
    answers: res.map((r) => ({ kind: "exact", label: `Residue at ${z} = ${toText(r.p.tree)}`, tree: r.v, at: r.p.tree })),
    verify: () => {
      const dmin = Math.min(...res.map((a) => Math.min(...res.filter((b) => b !== a).map((b) => cabsN({ re: a.p.v.re - b.p.v.re, im: a.p.v.im - b.p.v.im })), Infinity)));
      if (dmin < 0.2) return TCV([open("contour", "poles are too close together for the numeric check")]);
      return TCV(res.map((r) => checkCoef(fz, r.p.v, -1, r.v, `residue at ${toText(r.p.tree)}`)));
    },
  };
}
function cmdLaurent(node, env) {
  const f = node.args[0];
  if (!f || node.args.length < 3) throw fail("laurent(f, z, z0, order): terms of the Laurent series below (z - z0)^order");
  const z = varOf(node, 1);
  const z0 = C(node.args[2]);
  if (X.freeSymbols(z0).size) throw fail("the centre must be a number");
  const order = node.args[3] ? node.args[3] : X.num(2);
  if (!X.isInt(order) || order.v.n < -6n || order.v.n > 8n) throw fail("the order must be an integer between -6 and 8");
  const ord = Number(order.v.n);
  const probe = laurentAt(f, z, z0, 1);
  const m = Math.max(0, probe.m);
  const K = ord + m;
  if (K <= 0) throw fail("no terms below that order");
  const { coeffs } = laurentAt(f, z, z0, Math.max(1, K - m));
  const w = X.isZero(z0) ? S(z) : X.sub(S(z), z0);
  const terms = [];
  const used = [];
  for (let k = 0; k < Math.min(coeffs.length, K); k++) {
    const e = k - m;
    if (e >= ord) break;
    const c = tidyTrig(coeffs[k]);
    used.push({ e, c });
    if (isZeroExact(c) === true) continue;
    terms.push(X.mul(c, X.pow(w, X.num(e))));
  }
  const main = C(X.add(...terms));
  const tree = C(X.add(main, X.fn("O", X.pow(w, X.num(ord)))));
  env.log.add({ rule: "complex.laurent", title: "Laurent series", why: `Expand numerator and denominator in powers of ${toText(w)} and divide the series${m ? `; the pole has order ${m}` : ""}.`, before: f, after: tree });
  const z0n = cnumOf(z0);
  const fz = cfn(f, z);
  return {
    answers: [{ kind: "exact", label: "Laurent series", tree }],
    verify: () => TCV(used.map(({ e, c }) => checkCoef(fz, z0n, e, c, `coefficient of ${toText(w)}^${e}`))),
  };
}
function cmdContourint(node, env) {
  const f = node.args[0];
  if (!f || node.args.length !== 4) throw fail("contourint(f, z, center, radius): positively oriented circle");
  const z = varOf(node, 1);
  const c = C(node.args[2]), R = C(node.args[3]);
  const cn = cnumOf(c), Rn = numOf(R);
  if (!cn || !(Rn > 0)) throw fail("the centre must be a number and the radius positive");
  const extra = [...X.freeSymbols(f)].filter((v) => v !== z);
  if (extra.length) throw fail(`the function has symbols other than ${z}`);
  const poles = polesOf(f, z);
  const inside = [];
  for (const p of poles) {
    const d = cabsN({ re: p.v.re - cn.re, im: p.v.im - cn.im });
    if (Math.abs(d - Rn) < 1e-9 * Math.max(1, Rn)) {
      const exactOn = isZeroExact(X.sub(X.mul(X.sub(p.tree, c), X.fn("conj", X.sub(p.tree, c))), X.pow(R, X.TWO)));
      void exactOn;
      throw fail(`the pole z = ${toText(p.tree)} lies on the contour, so the integral is not defined (only a principal value would be)`);
    }
    if (d < Rn) inside.push(p);
  }
  const parts = [];
  for (const p of inside) {
    const { m, value } = residueExact(f, z, p.tree);
    if (m > 0) parts.push({ p, v: value });
  }
  const sum = C(X.add(...parts.map((q) => q.v)));
  const val = nice(tidyTrig(C(X.mul(X.TWO, X.PI, X.I, sum))));
  env.log.add({ rule: "complex.contour", title: "Residue theorem", why: parts.length ? `Poles inside the circle: ${parts.map((q) => `${toText(q.p.tree)} (residue ${toText(q.v)})`).join(", ")}; the integral is 2 pi i times the sum of the residues.` : "No pole lies inside the circle, so by Cauchy's theorem the integral is 0.", before: f, after: val });
  const fz = cfn(f, z);
  return {
    answers: [{ kind: "exact", label: "Contour integral", tree: val }],
    verify: () => {
      const trap = (Npts) => {
        let sr = 0, si = 0;
        for (let j = 0; j < Npts; j++) {
          const th = (2 * Math.PI * j) / Npts;
          const w = { re: Rn * Math.cos(th), im: Rn * Math.sin(th) };
          const v = fz(cn.re + w.re, cn.im + w.im);
          if (!v || !Number.isFinite(v.re) || !Number.isFinite(v.im)) return null;
          const p = cmulN(v, { re: -w.im, im: w.re }); // dz = i w dtheta
          sr += p.re; si += p.im;
        }
        return { re: (sr * 2 * Math.PI) / Npts, im: (si * 2 * Math.PI) / Npts };
      };
      const a = trap(2048), b = trap(4096);
      const want = cnumOf(val);
      if (!a || !b || !want) return TCV([open("trapezoid", "f could not be evaluated on the circle")]);
      const sc = Math.max(1, cabsN(want));
      if (cabsN({ re: a.re - b.re, im: a.im - b.im }) > 1e-9 * sc) return TCV([open("trapezoid", "the trapezoid rule on the circle did not converge (a pole is close to the contour)")]);
      return TCV([cabsN({ re: b.re - want.re, im: b.im - want.im }) < 1e-8 * sc ? pass("trapezoid", `the trapezoid rule on the circle (4096 points) gives ${fmtC(b)}`) : bad("trapezoid", `the trapezoid rule on the circle gives ${fmtC(b)}, not ${fmtC(want)}`)]);
    },
  };
}
// real part of an exact expression with real symbols: (V + conj V)/2 via I -> -I
const conjT = (u) => X.replace(u, X.I, X.neg(X.I));
function cmdResidueint(node, env) {
  const f0 = node.args[0];
  if (!f0) throw fail("residueint(f): integral of f over the whole real line");
  const x = varOf(node, 1, "x");
  const extra = [...X.freeSymbols(f0)].filter((v) => v !== x);
  if (extra.length) throw fail(`the integrand has symbols other than ${x}`);
  const f = C(f0);
  // f = R(x) or R(x) cos(a x) / sin(a x)
  let R = f, osc = null, a = null;
  const fs = f.k === "mul" ? f.args : [f];
  const trig = fs.filter((q) => q.k === "fn" && (q.name === "cos" || q.name === "sin"));
  if (trig.length > 1) throw fail("only one factor cos(a x) or sin(a x) is supported");
  if (trig.length === 1) {
    const arg = C(trig[0].args[0]);
    const k = C(D(arg, x));
    if (X.hasSym(k, x) || isZeroExact(C(X.sub(arg, X.mul(k, S(x))))) !== true) throw fail("the trigonometric factor must be cos(a x) or sin(a x)");
    a = k; osc = trig[0].name;
    R = C(X.mul(...fs.filter((q) => q !== trig[0])));
    if (numOf(a) < 0) { a = C(X.neg(a)); if (osc === "sin") R = C(X.neg(R)); }
  }
  const { g, h } = splitGH(R);
  const gp = P.fromTree(C(expand(g, ctx())), x), hp = P.fromTree(C(expand(h, ctx())), x);
  if (!gp || !hp) throw fail("the integrand must be a rational function (optionally times cos(a x) or sin(a x))");
  const degDiff = (hp.length - 1) - (gp.length - 1);
  if (osc ? degDiff < 1 : degDiff < 2) throw fail(osc ? "the rational factor must decay (degree of the denominator > degree of the numerator)" : "the integral does not converge absolutely (the denominator must have degree at least 2 more than the numerator), so it is not evaluated");
  const zs = "z";
  const Rz = C(X.subs(R, { [x]: S(zs) }));
  const poles = polesOf(Rz, zs);
  if (poles.some((p) => Math.abs(p.v.im) < 1e-12)) throw fail("the integrand has a pole on the real axis, so the integral diverges");
  const upper = poles.filter((p) => p.v.im > 0);
  const G = osc ? C(X.mul(Rz, X.exp(X.mul(X.I, a, S(zs))))) : Rz;
  const parts = upper.map((p) => ({ p, v: residueExact(G, zs, p.tree).value }));
  let V = C(X.mul(X.TWO, X.PI, X.I, X.add(...parts.map((q) => q.v))));
  if (osc === "cos") V = C(X.div(X.add(V, conjT(V)), X.TWO));
  if (osc === "sin") V = C(X.div(X.sub(V, conjT(V)), X.mul(X.TWO, X.I)));
  V = nice(tidyTrig(C(expand(V, ctx()))));
  if (hasI(V)) { const V2 = safe(() => nice(C(together(V, ctx())))); if (V2 && !hasI(V2)) V = V2; }
  if (hasI(V)) throw fail("the value could not be brought to real form");
  env.log.add({ rule: "complex.realint", title: "Close the contour in the upper half-plane", why: `${osc ? `Write ${osc}(${toText(a)} x) through e^(i ${toText(a)} z) (Jordan's lemma)` : "The integrand decays like 1/|z|^2"}; the integral is 2 pi i times the residues at the poles in the upper half-plane: ${parts.map((q) => toText(q.p.tree)).join(", ")}.`, before: f0, after: V });
  const fe = (() => { const g2 = forEval(f0); return (t) => evalR(g2, { [x]: t }); })();
  return {
    answers: valueAnswers("Integral", V),
    verify: () => {
      let ref;
      if (!osc) ref = quadRealLine(fe);
      else {
        const an = numOf(a);
        const Rfe = (() => { const g2 = forEval(R); return (t) => evalR(g2, { [x]: t }); })();
        ref = osc === "cos" ? oscIntegral((t) => Rfe(t) + Rfe(-t), an, Math.cos, []) : oscIntegral((t) => Rfe(t) - Rfe(-t), an, Math.sin, []);
      }
      const want = numOf(V);
      if (!ref.ok || !Number.isFinite(want)) return TCV([open("quadrature", "the real-line quadrature did not converge")]);
      const tol = Math.max(1e-9, 50 * (ref.err || 0));
      if (tol > 1e-5) return TCV([open("quadrature", "the real-line quadrature is not accurate enough")]);
      return TCV([Math.abs(ref.value - want) <= tol * Math.max(1, Math.abs(want)) ? pass("quadrature", `quadrature over the real line gives ${fmt(ref.value)}`) : bad("quadrature", `quadrature over the real line gives ${fmt(ref.value)}, not ${fmt(want)}`)]);
    },
  };
}

// ------------------------------------------------------------------ Cauchy-Riemann
// [re, im] of an expression in z (x, y real)
function reIm(u, z) {
  const x = S("x"), y = S("y");
  const go = (w) => {
    if (!X.hasSym(w, z) && !X.contains(w, X.I)) return [w, X.ZERO];
    switch (w.k) {
      case "const": if (w === X.I) return [X.ZERO, X.ONE]; return [w, X.ZERO];
      case "sym": return w.name === z ? [x, y] : [w, X.ZERO];
      case "add": { const ps = w.args.map(go); return [X.add(...ps.map((p) => p[0])), X.add(...ps.map((p) => p[1]))]; }
      case "mul": { let acc = [X.ONE, X.ZERO]; for (const a of w.args) { const [c, d] = go(a); acc = [X.sub(X.mul(acc[0], c), X.mul(acc[1], d)), X.add(X.mul(acc[0], d), X.mul(acc[1], c))]; } return acc; }
      case "pow": {
        const [b, e] = w.args;
        if (b === X.E) { const [p, q] = go(e); const ea = X.exp(p); return [X.mul(ea, X.fn("cos", q)), X.mul(ea, X.fn("sin", q))]; }
        if (X.isInt(e)) {
          const n = Number(e.v.n);
          if (Math.abs(n) > 12) throw fail("power too large");
          let [c, d] = go(b);
          if (n < 0) { const den = X.add(X.pow(c, X.TWO), X.pow(d, X.TWO)); [c, d] = [X.div(c, den), X.div(X.neg(d), den)]; }
          let acc = [X.ONE, X.ZERO];
          for (let i = 0; i < Math.abs(n); i++) acc = [X.sub(X.mul(acc[0], c), X.mul(acc[1], d)), X.add(X.mul(acc[0], d), X.mul(acc[1], c))];
          return acc;
        }
        if (!X.hasSym(e, z) && e.k === "num") {
          // real power of a real quantity only
          const [c, d] = go(b);
          if (isZeroExact(C(d)) === true) return [X.pow(c, e), X.ZERO];
        }
        throw fail("unsupported power for the real / imaginary split");
      }
      case "fn": {
        const n = w.name;
        if (n === "conj") { const [c, d] = go(w.args[0]); return [c, X.neg(d)]; }
        if (n === "abs") { const [c, d] = go(w.args[0]); return [X.sqrt(X.add(X.pow(c, X.TWO), X.pow(d, X.TWO))), X.ZERO]; }
        if (n === "re") { const [c] = go(w.args[0]); return [c, X.ZERO]; }
        if (n === "im") { const [, d] = go(w.args[0]); return [d, X.ZERO]; }
        const [p, q] = go(w.args[0]);
        if (n === "sin") return [X.mul(X.fn("sin", p), X.fn("cosh", q)), X.mul(X.fn("cos", p), X.fn("sinh", q))];
        if (n === "cos") return [X.mul(X.fn("cos", p), X.fn("cosh", q)), X.neg(X.mul(X.fn("sin", p), X.fn("sinh", q)))];
        if (n === "exp") { const ea = X.exp(p); return [X.mul(ea, X.fn("cos", q)), X.mul(ea, X.fn("sin", q))]; }
        if (n === "sinh") return [X.mul(X.fn("sinh", p), X.fn("cos", q)), X.mul(X.fn("cosh", p), X.fn("sin", q))];
        if (n === "cosh") return [X.mul(X.fn("cosh", p), X.fn("cos", q)), X.mul(X.fn("sinh", p), X.fn("sin", q))];
        throw fail(`${n} is not supported in the Cauchy-Riemann test`);
      }
      default: throw fail("unsupported expression");
    }
  };
  const [a, b] = go(u);
  return [tidyTrig(C(a)), tidyTrig(C(b))];
}
function crCore(u, v, env, fLabel) {
  const ux = tidyTrig(D(u, "x")), uy = tidyTrig(D(u, "y")), vx = tidyTrig(D(v, "x")), vy = tidyTrig(D(v, "y"));
  const e1 = tidyTrig(C(X.sub(ux, vy))), e2 = tidyTrig(C(X.add(uy, vx)));
  const z1 = isZ(e1), z2 = isZ(e2);
  env.log.add({ rule: "complex.cr", title: "Cauchy-Riemann equations", why: `u = ${toText(u)}, v = ${toText(v)}: u_x - v_y = ${toText(e1)}, u_y + v_x = ${toText(e2)}.`, before: fLabel, after: X.tuple(e1, e2) });
  if (z1 === true && z2 === true) return { holds: true, e1, e2 };
  if (z1 === null && z2 === null) throw fail("could not decide whether the Cauchy-Riemann equations hold");
  // where do they hold?
  const eqs = [e1, e2].filter((e, i) => [z1, z2][i] !== true);
  let where = null;
  if (eqs.length === 1) {
    const r = orchestrate(X.eq(eqs[0], X.ZERO), { timeLimit: 4000, crossCheck: false, variable: [...X.freeSymbols(eqs[0])].length === 1 ? [...X.freeSymbols(eqs[0])][0] : undefined });
    if (r.ok && r.verification.status === "passed" && r.answers.length === 1 && r.answers[0].kind === "exact" && X.freeSymbols(eqs[0]).size === 1) where = X.eq(S([...X.freeSymbols(eqs[0])][0]), r.answers[0].tree);
    else if (!X.freeSymbols(eqs[0]).size) where = X.FALSE;
    else where = X.eq(eqs[0], X.ZERO);
  } else {
    const names = sortVars(new Set([...X.freeSymbols(eqs[0]), ...X.freeSymbols(eqs[1])]));
    if (!names.length) where = X.FALSE;
    else {
      const r = orchestrate(X.system(X.eq(eqs[0], X.ZERO), X.eq(eqs[1], X.ZERO)), { timeLimit: 5000, crossCheck: false, variable: names });
      if (r.noSolution) where = X.FALSE;
      else if (r.ok && r.verification.status === "passed" && r.answers.every((a) => a.kind === "solution")) {
        const pts = r.answers.map((a) => X.and(...["x", "y"].map((n) => { const m = new Map(a.values); return m.has(n) ? X.eq(S(n), m.get(n)) : null; }).filter(Boolean)));
        where = pts.length === 1 ? pts[0] : X.or(...pts);
      }
    }
  }
  return { holds: false, e1, e2, where };
}
// numeric certificate: directional complex derivatives of F(x, y) = u + i v
function crNumeric(ue, ve, holds, where) {
  const quot = (p, dir) => {
    const h = 1e-4;
    const F = (x, y) => ({ re: ue({ x, y }), im: ve({ x, y }) });
    const a = F(p.x + h * dir.re, p.y + h * dir.im), b = F(p.x - h * dir.re, p.y - h * dir.im);
    const num = { re: (a.re - b.re) / (2 * h), im: (a.im - b.im) / (2 * h) };
    const den = dir;
    const dd = den.re * den.re + den.im * den.im;
    return { re: (num.re * den.re + num.im * den.im) / dd, im: (num.im * den.re - num.re * den.im) / dd };
  };
  const pts = [{ x: 0.63, y: 0.41 }, { x: -1.17, y: 0.83 }, { x: 1.49, y: -0.72 }, { x: -0.38, y: -1.26 }];
  let agree = 0, disagree = 0;
  for (const p of pts) {
    const q1 = quot(p, { re: 1, im: 0 }), q2 = quot(p, { re: 0, im: 1 }), q3 = quot(p, { re: Math.SQRT1_2, im: Math.SQRT1_2 });
    if (![q1, q2, q3].every((q) => Number.isFinite(q.re) && Number.isFinite(q.im))) continue;
    const sc = Math.max(1, cabsN(q1));
    const d = Math.max(cabsN({ re: q1.re - q2.re, im: q1.im - q2.im }), cabsN({ re: q1.re - q3.re, im: q1.im - q3.im }));
    if (d < 1e-6 * sc) agree++; else if (d > 1e-3 * sc) disagree++;
  }
  if (holds) return agree >= 3 && !disagree ? pass("difference-quotients", `the difference quotient (f(z + h) - f(z - h))/(2h) is the same along 3 directions at ${agree} points`) : bad("difference-quotients", "the complex difference quotients depend on the direction");
  if (!disagree) return bad("difference-quotients", "the difference quotients do not depend on the direction, so the function looks analytic");
  const checks = [pass("difference-quotients", `the complex difference quotient depends on the direction at ${disagree} of 4 points`)];
  void where;
  return checks[0];
}
function cmdAnalytic(node, env) {
  const f = node.args[0];
  if (!f || ["eq", "vector", "tuple", "matrix"].includes(f.k)) throw fail("analytic(f(z))");
  const z = varOf(node, 1);
  const extra = [...X.freeSymbols(f)].filter((v) => v !== z);
  if (extra.length) throw fail(`the function has symbols other than ${z}`);
  if (z === "x" || z === "y") throw fail("use z as the complex variable");
  const [u, v] = reIm(f, z);
  const r = crCore(u, v, env, f);
  // verifier: the ORIGINAL f evaluated with complex arithmetic (not the u, v split used above)
  const fz = cfn(f, z);
  const ue = (p) => { const w = fz(p.x, p.y); return w ? w.re : NaN; }, ve = (p) => { const w = fz(p.x, p.y); return w ? w.im : NaN; };
  const answers = [{ kind: "exact", label: "Analytic", tree: r.holds ? X.TRUE : X.FALSE }];
  if (!r.holds && r.where && r.where !== X.FALSE) answers.push({ kind: "set", label: "Cauchy-Riemann equations hold only where", tree: r.where });
  return {
    answers, verify: () => {
      const checks = [crNumeric(ue, ve, r.holds, r.where)];
      if (!r.holds && r.where && r.where !== X.FALSE) checks.push(whereCheck(u, v, r.where));
      return TCV(checks);
    },
  };
}
// at points of the claimed set the finite-difference CR residuals vanish
function whereCheck(u, v, where) {
  const ue = (() => { const g = forEval(u); return (p) => evalR(g, p); })(), ve = (() => { const g = forEval(v); return (p) => evalR(g, p); })();
  const d = (fn, p, k) => { const h = 1e-4; const a = { ...p, [k]: p[k] + h }, b = { ...p, [k]: p[k] - h }; return (fn(a) - fn(b)) / (2 * h); };
  const res = (p) => Math.hypot(d(ue, p, "x") - d(ve, p, "y"), d(ue, p, "y") + d(ve, p, "x"));
  // sample points on the set: solve for y (or x) from simple equations
  const pts = [];
  const eqs = where.k === "and" ? where.args : [where];
  if (where.k === "or") return open("where", "several regions; not checked numerically");
  const fixed = {};
  for (const e of eqs) if (e.k === "eq" && e.args[0].k === "sym" && !X.freeSymbols(e.args[1]).size) fixed[e.args[0].name] = numOf(e.args[1]);
  for (const t of [-1.3, 0.4, 1.7]) {
    const p = { x: fixed.x !== undefined ? fixed.x : t, y: fixed.y !== undefined ? fixed.y : 0.9 * t + 0.2 };
    if (eqs.every((e) => e.k === "eq" && e.args[0].k === "sym" && fixed[e.args[0].name] !== undefined)) pts.push(p);
  }
  if (!pts.length) return open("where", "the set was not checked numerically");
  const ok = pts.every((p) => res(p) < 1e-6);
  return ok ? pass("where", "the finite-difference Cauchy-Riemann residuals vanish at sample points of the set") : bad("where", "the Cauchy-Riemann equations fail at a point of the claimed set");
}
function cmdCauchyRiemann(node, env) {
  const [u0, v0] = node.args;
  if (!u0 || !v0) throw fail("cauchyriemann(u, v) with u, v functions of x and y");
  const extra = [...X.freeSymbols(u0), ...X.freeSymbols(v0)].filter((s) => s !== "x" && s !== "y");
  if (extra.length) throw fail("u and v must be functions of x and y");
  const u = C(u0), v = C(v0);
  const r = crCore(u, v, env, X.tuple(u, v));
  const ue = (() => { const g = forEval(u); return (p) => evalR(g, p); })(), ve = (() => { const g = forEval(v); return (p) => evalR(g, p); })();
  const answers = [{ kind: "exact", label: "Cauchy-Riemann equations hold everywhere", tree: r.holds ? X.TRUE : X.FALSE }];
  if (!r.holds && r.where && r.where !== X.FALSE) answers.push({ kind: "set", label: "Cauchy-Riemann equations hold only where", tree: r.where });
  return {
    answers, verify: () => {
      const checks = [crNumeric(ue, ve, r.holds, r.where)];
      if (!r.holds && r.where && r.where !== X.FALSE) checks.push(whereCheck(u, v, r.where));
      return TCV(checks);
    },
  };
}

export const COMPLEX = { residue: cmdResidue, laurent: cmdLaurent, contourint: cmdContourint, residueint: cmdResidueint, analytic: cmdAnalytic, cauchyriemann: cmdCauchyRiemann };
void numerDenom; void open;
