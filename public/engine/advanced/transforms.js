// Integral transforms: Laplace transform and its inverse, linear constant-coefficient IVPs by the
// Laplace transform, Fourier series on [-L, L], Fourier transforms of standard functions and the
// Z-transform.
//
// Solver: sin / cos / sinh / cosh are rewritten as (complex) exponentials, so every supported input
// becomes a sum c t^n e^(k t) (Laplace) or c n^m r^n (Z); the transform of each term is a table
// entry and the sum is brought back to a real rational function. The inverse Laplace transform
// uses partial fractions over Q and a table of linear and quadratic factors.
// Verifier (independent): numeric forward transforms of the ORIGINAL input (tanh-sinh on [0, oo),
// Gauss-Legendre with alternating-series acceleration for Fourier integrals, partial sums for the
// Z-transform), exact substitution of an IVP solution into the ODE, and quadrature of Fourier
// coefficients for n = 1..8.

import { definiteIntegral } from "../calc/int-definite.js";
import { detectODE } from "../calc/ode.js";
import { apartTerms, cancel } from "../poly-apart.js";
import * as P from "../poly-core.js";
import { numDen } from "../poly-factor.js";
import * as N from "../num.js";
import {
  X, toText, TCV, fail, safe, pass, bad, open, fmt, fmtC, C, D, nice, tidyTrig, isZeroExact, expand, together, numerDenom,
  valueAnswers, evalR, evalZ, forEval, envFn, glPanel, quad1, quadHalfLine, numOf, cnumOf, closeTo, sortVars,
} from "./util.js";
import { makeCtx } from "../simplify.js";

const S = X.sym;
const ctx = () => makeCtx({ budget: { ops: 600000 } });
const E_ = (u) => X.pow(X.E, u);
const hasI = (u) => X.contains(u, X.I);
const factorial = (n) => { let r = 1n; for (let k = 2n; k <= BigInt(n); k++) r *= k; return X.num(N.Q(r)); };

// sin, cos, sinh, cosh -> exponentials (complex for sin / cos)
function toExp(u) {
  return X.mapTree(u, (w) => {
    if (w.k !== "fn" || w.args.length !== 1) return w;
    const a = w.args[0];
    const iA = X.mul(X.I, a);
    switch (w.name) {
      case "sin": return X.div(X.sub(E_(iA), E_(X.neg(iA))), X.mul(X.TWO, X.I));
      case "cos": return X.div(X.add(E_(iA), E_(X.neg(iA))), X.TWO);
      case "sinh": return X.div(X.sub(E_(a), E_(X.neg(a))), X.TWO);
      case "cosh": return X.div(X.add(E_(a), E_(X.neg(a))), X.TWO);
      default: return w;
    }
  });
}
// u = k v + c with k, c free of v -> { k, c } or null
function linearIn(u, v) {
  const k = C(D(u, v));
  if (X.hasSym(k, v)) return null;
  let c = C(X.sub(u, X.mul(k, S(v))));
  if (X.hasSym(c, v)) c = C(expand(c, ctx()));
  if (X.hasSym(c, v)) return null;
  return { k, c };
}
// term -> { coef, n, k } for coef * v^n * e^(k v); null when the term has another shape
function splitTerm(term, v) {
  const fs = term.k === "mul" ? term.args : [term];
  const coef = [], ks = [];
  let n = 0;
  for (const f of fs) {
    if (!X.hasSym(f, v)) { coef.push(f); continue; }
    if (f.k === "sym" && f.name === v) { n += 1; continue; }
    if (f.k === "pow" && f.args[0].k === "sym" && f.args[0].name === v && X.isInt(f.args[1]) && f.args[1].v.n > 0n) { n += Number(f.args[1].v.n); continue; }
    if (f.k === "pow" && f.args[0] === X.E) { const l = linearIn(f.args[1], v); if (!l) return null; ks.push(l.k); coef.push(E_(l.c)); continue; }
    if (f.k === "pow" && !X.hasSym(f.args[0], v)) { // r^(k v + c)
      const l = linearIn(f.args[1], v); if (!l) return null;
      ks.push(X.mul(l.k, X.fn("ln", f.args[0]))); coef.push(X.pow(f.args[0], l.c)); continue;
    }
    return null;
  }
  return { coef: C(X.mul(...coef)), n, k: C(X.add(...ks)) };
}
function expTerms(f, v) {
  const e = C(expand(C(toExp(f)), ctx()));
  const terms = e.k === "add" ? e.args : [e];
  const out = [];
  for (const t of terms) { const s = splitTerm(t, v); if (!s) return null; out.push(s); }
  return out;
}
// bring a sum that may contain I back to a real presentation
function realForm(u, v) {
  const cands = [];
  const a = safe(() => nice(u));
  if (a) cands.push(a);
  const b = safe(() => { const [n, d] = numerDenom(C(together(C(u), ctx()))); return C(X.div(C(expand(C(n), ctx())), C(expand(C(d), ctx())))); });
  if (b) cands.push(b);
  const good = cands.filter((c) => !hasI(c) && c !== X.UNDEF && !X.contains(c, X.UNDEF));
  if (!good.length) return null;
  let best = good[0];
  for (const c of good) {
    const cc = v ? safe(() => cancel(c, v)) : null;
    const ks = [c, safe(() => factorDen(c))];
    if (cc && cc.tree) ks.push(cc.tree, safe(() => factorDen(cc.tree)), safe(() => C(X.div(cc.numerator, safe(() => sqf(cc.denominator, v)) || cc.denominator))));
    for (const k of ks) if (k && !hasI(k) && !X.contains(k, X.UNDEF) && toText(k).length < toText(best).length) best = k;
  }
  return best;
}
// denominator d = (a v + b)^m presentation when it is a perfect power of a linear factor
function sqf(d, v) {
  const p = P.fromTree(C(expand(C(d), ctx())), v);
  if (!p || p.length < 3) return null;
  const m = p.length - 1;
  const lead = p[m], b = N.div(p[m - 1], N.mul(N.Q(m), lead)); // d = lead (v + b)^m ?
  const cand = C(X.mul(X.num(lead), X.pow(X.add(X.sym(v), X.num(b)), X.num(m))));
  return isZeroExact(X.sub(C(expand(cand, ctx())), C(expand(C(d), ctx())))) === true ? cand : null;
}
// numerator / factored-denominator presentation (keeps (s - 2)^4 instead of its expansion)
function factorDen(u) {
  const [n, d] = numerDenom(C(together(C(u), ctx())));
  return C(X.div(C(expand(C(n), ctx())), d));
}

// ------------------------------------------------------------------ Laplace transform
function heavisideSplit(f, t) {
  // sum of terms; a term with a factor heaviside(t - d) (d >= 0) is shifted
  const e = C(expand(C(f), ctx()));
  const terms = e.k === "add" ? e.args : [e];
  const groups = new Map();
  for (const term of terms) {
    const fs = term.k === "mul" ? term.args : [term];
    let d = X.ZERO, rest = [];
    let hv = 0;
    for (const g of fs) {
      if (g.k === "fn" && g.name === "heaviside") {
        const l = linearIn(g.args[0], t);
        if (!l || l.k !== X.ONE) throw fail("heaviside(t - a) must have argument t - a");
        d = C(X.neg(l.c)); hv++;
      } else rest.push(g);
    }
    if (hv > 1) throw fail("products of step functions are not supported");
    const key = d.id;
    if (!groups.has(key)) groups.set(key, { d, parts: [] });
    groups.get(key).parts.push(X.mul(...rest));
  }
  return [...groups.values()].map((g) => ({ d: g.d, f: C(X.add(...g.parts)) }));
}
function laplaceCore(f, t, s) {
  const terms = expTerms(f, t);
  if (!terms) return null;
  const parts = [];
  let sigma = -Infinity;
  for (const { coef, n, k } of terms) {
    parts.push(X.mul(coef, factorial(n), X.pow(X.sub(S(s), k), X.num(-(n + 1)))));
    const kv = cnumOf(k);
    if (!kv) return null;
    sigma = Math.max(sigma, kv.re);
  }
  return { F: C(X.add(...parts)), sigma };
}
function laplaceNumeric(f, t, s0, breaks, tailLen) {
  const fe = envFn(f);
  const g = (x) => fe({ [t]: x }) * Math.exp(-s0 * x);
  const pts = [0, ...breaks.filter((b) => b > 0).sort((a, b) => a - b)];
  let total = 0, err = 0;
  for (let i = 0; i + 1 < pts.length; i++) { const r = quad1(g, pts[i], pts[i + 1], { m: 16, panels: 8 }); if (!r.ok) return { ok: false }; total += r.value; err += r.err; }
  // tail: e^(-(s0 - sigma) t) with s0 - sigma >= 1.3, so beyond 60/(s0 - sigma) it is below e^(-60) relative
  const last = pts[pts.length - 1];
  const r = quad1(g, last, last + tailLen, { m: 16, panels: 48 });
  if (!r.ok) return { ok: false };
  return { ok: true, value: total + r.value, err: err + r.err };
}
function laplaceVerify(f, F, t, s, sigma, breaks, what) {
  const checks = [];
  for (const off of [1.3, 2.7, 4.1]) {
    const s0 = Math.max(sigma, 0) + off;
    const ref = laplaceNumeric(f, t, s0, breaks, 60 / (s0 - Math.max(sigma, 0)) + 20);
    const want = evalR(forEval(F), { [s]: s0 });
    if (!ref.ok || !Number.isFinite(want)) { checks.push(open("numeric-transform", `the numeric transform at s = ${fmt(s0)} did not converge`)); continue; }
    checks.push(closeTo(want, ref.value, 1e-7) ? pass("numeric-transform", `integral of ${what} e^(-s t) dt at s = ${fmt(s0)} is ${fmt(ref.value)} by tanh-sinh quadrature`) : bad("numeric-transform", `at s = ${fmt(s0)} the numeric transform is ${fmt(ref.value)}, not ${fmt(want)}`));
  }
  return checks;
}
function cmdLaplace(node, env) {
  const f = node.args[0];
  if (!f || ["eq", "vector", "tuple", "matrix"].includes(f.k)) throw fail("laplace(f(t)) needs a function of t");
  const t = node.args[1] && node.args[1].k === "sym" ? node.args[1].name : (X.hasSym(f, "t") || !X.freeSymbols(f).size ? "t" : sortVars(X.freeSymbols(f))[0]);
  const s = node.args[2] && node.args[2].k === "sym" ? node.args[2].name : "s";
  const extra = [...X.freeSymbols(f)].filter((v) => v !== t);
  if (extra.length) throw fail(`the function has symbols other than ${t} (${extra.join(", ")})`);
  const groups = heavisideSplit(f, t);
  const parts = [];
  let sigma = -Infinity;
  const breaks = [];
  for (const g of groups) {
    const dv = numOf(g.d);
    if (!(dv >= 0)) throw fail("step functions heaviside(t - a) need a >= 0");
    const shifted = X.isZero(g.d) ? g.f : C(X.subs(g.f, { [t]: X.add(S(t), g.d) }));
    const r = laplaceCore(shifted, t, s);
    if (!r) throw fail(`no Laplace transform rule applies to ${toText(g.f)} (supported: sums of t^n e^(a t), sin, cos, sinh, cosh with linear arguments, and step functions)`);
    parts.push(X.isZero(g.d) ? r.F : X.mul(E_(X.neg(X.mul(g.d, S(s)))), r.F));
    sigma = Math.max(sigma, r.sigma);
    if (dv > 0) breaks.push(dv);
  }
  let F = realForm(X.add(...parts), s);
  if (!F) throw fail("the transform could not be brought to a real form");
  env.log.add({ rule: "laplace.table", title: "Laplace transform term by term", why: "Write sin, cos, sinh and cosh as exponentials; L{t^n e^(a t)} = n!/(s - a)^(n + 1); a step heaviside(t - a) multiplies by e^(-a s) after shifting t -> t + a.", before: f, after: F });
  return {
    answers: [{ kind: "exact", label: "Laplace transform", tree: F }],
    conditions: [X.rel(">", S(s), X.num(Math.max(0, Math.ceil(sigma === -Infinity ? 0 : sigma))) )].filter(() => false),
    verify: () => TCV(laplaceVerify(f, F, t, s, sigma, breaks, "f(t)")),
  };
}

// ------------------------------------------------------------------ inverse Laplace transform
const qv = (q) => X.num(q);
function invRational(R, s, t) {
  // returns { f, poles: [real parts] } or throws
  const [nt, dt] = numDen(C(together(C(R), ctx())));
  const n = P.fromTree(C(expand(nt, ctx())), s), d = P.fromTree(C(expand(dt, ctx())), s);
  if (!n || !d || !d.length) throw fail("the transform must be a rational function of s with rational coefficients (times e^(-a s))");
  const ap = apartTerms(n, d);
  if (ap.poly.length) throw fail("the transform has a polynomial part (its inverse involves the Dirac delta), which is not supported");
  const parts = [], re = [];
  const T = S(t);
  for (const { numer, factor, power } of ap.terms) {
    const lead = factor[factor.length - 1];
    if (factor.length === 2) {
      // numer / (b s + c)^m = (numer/b^m) / (s - a)^m, a = -c/b
      const b = lead, a = N.neg(N.div(factor[0], b));
      const coef = N.div(numer[0], N.pow ? N.pow(b, power) : powQ(b, power));
      parts.push(X.mul(qv(coef), X.pow(T, X.num(power - 1)), X.recip(factorial(power - 1)), E_(X.mul(qv(a), T))));
      re.push(Number(a.n) / Number(a.d));
      continue;
    }
    if (factor.length === 3 && power <= 2) {
      // (A s + B) / (b (s^2 + p s + q))^m
      const b = lead;
      const p = N.div(factor[1], b), q = N.div(factor[0], b);
      const bm = powQ(b, power);
      const A = N.div(numer[1] || N.ZERO, bm), B = N.div(numer[0] || N.ZERO, bm);
      const h = N.div(p, N.Q(2));
      const disc = N.sub(q, N.mul(h, h)); // w^2 (> 0) or -k^2 (< 0)
      const B2 = N.sub(B, N.mul(A, h)); // A (s + h) + B2
      const eh = E_(X.mul(qv(N.neg(h)), T));
      re.push(-Number(h.n) / Number(h.d));
      if (N.sign(disc) > 0) {
        const w = C(X.sqrt(qv(disc))), wt = X.mul(w, T);
        if (power === 1) parts.push(X.mul(eh, X.add(X.mul(qv(A), X.fn("cos", wt)), X.mul(qv(B2), X.recip(w), X.fn("sin", wt)))));
        else parts.push(X.mul(eh, X.add(X.mul(qv(A), T, X.fn("sin", wt), X.recip(X.mul(X.TWO, w))), X.mul(qv(B2), X.sub(X.fn("sin", wt), X.mul(wt, X.fn("cos", wt))), X.recip(X.mul(X.TWO, X.pow(w, X.num(3))))))));
      } else if (N.sign(disc) < 0 && power === 1) {
        const k = C(X.sqrt(qv(N.neg(disc)))), kt = X.mul(k, T);
        parts.push(X.mul(eh, X.add(X.mul(qv(A), X.fn("cosh", kt)), X.mul(qv(B2), X.recip(k), X.fn("sinh", kt)))));
        re[re.length - 1] += Math.sqrt(-Number(disc.n) / Number(disc.d));
      } else throw fail("repeated irreducible quadratic factors with real roots are not supported");
      continue;
    }
    throw fail("the denominator has an irreducible factor of degree > 2 or a quadratic factor to a power > 2; not supported");
  }
  return { f: C(X.add(...parts)), sigma: re.length ? Math.max(...re) : 0 };
}
function powQ(b, m) { let r = N.ONE; for (let i = 0; i < m; i++) r = N.mul(r, b); return r; }
function cmdInvLaplace(node, env) {
  const F = node.args[0];
  if (!F || ["eq", "vector", "tuple", "matrix"].includes(F.k)) throw fail("invlaplace(F(s)) needs a function of s");
  const s = node.args[1] && node.args[1].k === "sym" ? node.args[1].name : "s";
  const t = node.args[2] && node.args[2].k === "sym" ? node.args[2].name : "t";
  const extra = [...X.freeSymbols(F)].filter((v) => v !== s);
  if (extra.length) throw fail(`the transform has symbols other than ${s} (${extra.join(", ")})`);
  // group terms by their e^(-a s) factor
  const e = C(expand(C(F), ctx()));
  const terms = e.k === "add" ? e.args : [e];
  const groups = new Map();
  for (const term of terms) {
    const fs = term.k === "mul" ? term.args : [term];
    let a = X.ZERO;
    const rest = [];
    for (const g of fs) {
      if (g.k === "pow" && g.args[0] === X.E && X.hasSym(g.args[1], s)) {
        const l = linearIn(g.args[1], s);
        if (!l || !X.isZero(l.c)) throw fail("exponential factors must be e^(-a s)");
        a = C(X.add(a, X.neg(l.k)));
      } else rest.push(g);
    }
    if (!X.isZero(a) && !(numOf(a) > 0)) throw fail("shift factors e^(-a s) need a > 0");
    if (!groups.has(a.id)) groups.set(a.id, { a, parts: [] });
    groups.get(a.id).parts.push(X.mul(...rest));
  }
  const pieces = [], breaks = [];
  let sigma = -Infinity;
  for (const g of groups.values()) {
    const R = C(X.add(...g.parts));
    if ([...X.freeSymbols(R)].some((v) => v !== s) || X.contains(R, X.E) && /ln|log/.test(toText(R))) throw fail("unsupported transform");
    const r = invRational(R, s, t);
    sigma = Math.max(sigma, r.sigma);
    if (X.isZero(g.a)) pieces.push(r.f);
    else { pieces.push(X.mul(C(X.subs(r.f, { [t]: X.sub(S(t), g.a) })), X.fn("heaviside", X.sub(S(t), g.a)))); breaks.push(numOf(g.a)); }
  }
  let f = C(X.add(...pieces));
  const ft = safe(() => tidyTrig(f));
  if (ft && !hasI(ft)) f = ft;
  env.log.add({ rule: "laplace.inverse", title: "Partial fractions and the table", why: "Split the rational part into partial fractions over Q; invert 1/(s - a)^m, (A s + B)/((s + h)^2 + w^2) and its square by the table; e^(-a s) shifts the result by a and multiplies by heaviside(t - a).", before: F, after: f });
  return { answers: [{ kind: "exact", label: "Inverse Laplace transform", tree: f }], verify: () => TCV(laplaceVerify(f, F, t, s, sigma, breaks, "the answer f(t)")) };
}

// ------------------------------------------------------------------ IVPs by Laplace
function cmdLapsolve(node, env) {
  const args = node.args;
  if (!args.length) throw fail("lapsolve(ode, initial conditions)");
  let info;
  try { info = detectODE(X.system(...args)); } catch (e) { if (e && e.code === "TIMEOUT") throw e; info = null; }
  if (!info || !info.odes || info.odes.length !== 1 || info.deps.length !== 1) throw fail("lapsolve needs one ODE in one unknown function, for example lapsolve(y'' + y = 0, y(0) = 1, y'(0) = 0)");
  const y = info.deps[0];
  let t = info.x;
  const Fode = info.odes[0].F;
  const order = info.order[y];
  const dsym = (k) => (k === 0 ? S(y) : S(`__D${k}_${y}`));
  const coeffs = [];
  for (let k = 0; k <= order; k++) {
    const c = C(D(Fode, dsym(k)));
    if (X.freeSymbols(c).size) throw fail("the Laplace method here needs constant coefficients");
    coeffs.push(c);
  }
  const zero = {}; for (let k = 0; k <= order; k++) zero[k === 0 ? y : `__D${k}_${y}`] = X.ZERO;
  const g = C(X.neg(X.subs(Fode, zero))); // sum c_k y^(k) = g(t)
  const lin = C(X.sub(Fode, X.add(...coeffs.map((c, k) => X.mul(c, dsym(k))), X.neg(g))));
  if (isZeroExact(lin) !== true) throw fail("the equation is not linear in the unknown function");
  // rename x -> t when the ODE does not mention x explicitly
  if (t === "x" && !X.hasSym(g, "x")) t = "t";
  const gt = t === info.x ? g : C(X.subs(g, { [info.x]: S(t) }));
  const ic = new Map();
  for (const c of info.ics || []) { if (c.dep !== y || !X.isZero(C(c.at))) throw fail("the initial conditions must be given at t = 0"); ic.set(c.m, C(c.value)); }
  for (let k = 0; k < order; k++) if (!ic.has(k)) throw fail(`missing initial condition for ${y}${"'".repeat(k)}(0)`);
  const s = "s", Ssym = S(s);
  let G = X.ZERO;
  if (!isZeroExact(gt)) {
    const L = laplaceCore(gt, t, s);
    if (!L) throw fail(`the forcing term ${toText(gt)} has no Laplace transform rule`);
    G = realForm(L.F, s);
    if (!G) throw fail("the forcing term transform could not be brought to real form");
  }
  // sum c_k (s^k Y - sum_{j<k} s^(k-1-j) y^(j)(0)) = G
  const Pk = X.add(...coeffs.map((c, k) => X.mul(c, X.pow(Ssym, X.num(k)))));
  const icTerms = [];
  coeffs.forEach((c, k) => { for (let j = 0; j < k; j++) icTerms.push(X.mul(c, X.pow(Ssym, X.num(k - 1 - j)), ic.get(j))); });
  const Y = C(together(C(X.div(X.add(G, ...icTerms), Pk)), ctx()));
  env.log.add({ rule: "laplace.ivp", title: "Transform the equation", why: `L{${y}^(k)} = s^k Y - s^(k-1) ${y}(0) - ... ; solving the algebraic equation gives Y(s).`, before: args[0], after: X.eq(S("Y"), Y) });
  const inv = cmdInvLaplace(X.fn("invlaplace", Y, Ssym, S(t)), env);
  const sol = inv.answers[0].tree;
  const yT = S(y);
  return {
    answers: [{ kind: "exact", label: `${y}(${t})`, tree: sol }],
    verify: () => {
      // exact certificate: substitute into the ODE and the initial conditions
      const ders = [sol];
      for (let k = 1; k <= order; k++) ders.push(C(D(ders[k - 1], t)));
      const res = C(X.sub(X.add(...coeffs.map((c, k) => X.mul(c, ders[k]))), gt));
      const z = isZeroExact(res);
      const checks = [];
      if (z === true) checks.push(pass("substitution", `substituting ${y}(${t}) into the equation gives 0 identically`, false));
      else {
        const re = envFn(res), sc = envFn(gt);
        const pts = [0.37, 0.81, 1.43, 2.05, 3.1];
        const vals = pts.map((p) => re({ [t]: p }));
        const ok = vals.every((v, i) => Number.isFinite(v) && Math.abs(v) < 1e-9 * Math.max(1, Math.abs(sc({ [t]: pts[i] }) || 0)));
        checks.push(ok ? pass("substitution", "substituting the answer into the equation leaves a residual below 1e-9 at 5 points") : bad("substitution", `substituting the answer leaves ${toText(res)}`));
      }
      for (let k = 0; k < order; k++) {
        const v = C(X.subs(ders[k], { [t]: X.ZERO }));
        checks.push(isZeroExact(X.sub(v, ic.get(k))) === true ? pass("initial-condition", `${y}${"'".repeat(k)}(0) = ${toText(ic.get(k))}`, false) : bad("initial-condition", `${y}${"'".repeat(k)}(0) is ${toText(v)}, not ${toText(ic.get(k))}`));
      }
      void yT;
      return TCV(checks);
    },
  };
}

// ------------------------------------------------------------------ Fourier series
// exact roots of w = 0 when w is linear in x, or |linear| + constant
function linRoots(w, x) {
  w = C(w);
  const l = linearIn(w, x);
  if (l && isZeroExact(l.k) !== true) return [C(X.div(X.neg(l.c), l.k))];
  if (w.k === "add") {
    const ab = w.args.filter((a) => a.k === "fn" && a.name === "abs" && X.hasSym(a, x));
    const rest = C(X.add(...w.args.filter((a) => !ab.includes(a))));
    if (ab.length === 1 && !X.hasSym(rest, x)) {
      const li = linearIn(ab[0].args[0], x);
      if (li && isZeroExact(li.k) !== true) return [C(X.div(X.sub(rest, li.c), li.k)), C(X.div(X.sub(X.neg(rest), li.c), li.k))];
    }
  }
  return [];
}
// breakpoints of abs(.), steps and piecewise conditions inside (lo, hi): [[value, tree]] sorted
function breakpoints(f, x, lo, hi) {
  const pts = new Map();
  const add = (w) => { for (const r of linRoots(w, x)) { const v = numOf(r); if (Number.isFinite(v) && v > lo + 1e-12 && v < hi - 1e-12 && ![...pts.keys()].some((k) => Math.abs(k - v) < 1e-12)) pts.set(v, r); } };
  const walk = (w) => {
    if (w.k === "fn" && (w.name === "abs" || w.name === "heaviside" || w.name === "sign")) add(w.args[0]);
    if (w.k === "rel" || w.k === "eq") add(X.sub(w.args[0], w.args[1]));
    for (const a of w.args) walk(a);
  };
  walk(f);
  return [...pts.entries()].sort((a, b) => a[0] - b[0]);
}
const ID = new Map();
// f restricted to (a, b): choose piecewise branches and signs of abs at the midpoint
function restrict(f, x, mid) {
  return C(X.mapTree(f, (w) => {
    if (w.k === "fn" && w.name === "abs") { const v = evalR(forEval(w.args[0]), { [x]: mid }); return v >= 0 ? w.args[0] : X.neg(w.args[0]); }
    if (w.k === "piecewise") {
      for (let i = 0; i < w.args.length; i += 2) {
        const cond = w.args[i + 1];
        if (cond === X.TRUE) return w.args[i];
        const tv = safe(() => evalR(forEval(X.piecewise(X.ONE, cond, X.ZERO, X.TRUE)), { [x]: mid }));
        if (tv === 1) return w.args[i];
      }
      return X.UNDEF;
    }
    return w;
  }));
}
function integerTrig(u, n) {
  // sin(k n pi) -> 0, cos(k n pi) -> (-1)^(k n) for integer k, n
  return C(X.mapTree(u, (w) => {
    if (w.k !== "fn" || (w.name !== "sin" && w.name !== "cos") || w.args.length !== 1) return w;
    const q = C(X.div(w.args[0], X.mul(S(n), X.PI)));
    if (!X.isInt(q)) return w;
    return w.name === "sin" ? X.ZERO : X.pow(X.NEG_ONE, X.mul(q, S(n)));
  }));
}
function cmdFourier(node, env) {
  const [f0, xv, Lv] = node.args;
  if (!f0 || !xv || xv.k !== "sym" || !Lv) throw fail("fourier(f, x, L): Fourier series of f on [-L, L]");
  const x = xv.name;
  const L = C(Lv);
  const Ln = numOf(L);
  if (!(Ln > 0) || X.freeSymbols(L).size) throw fail("L must be a positive number");
  const extra = [...X.freeSymbols(f0)].filter((v) => v !== x);
  if (extra.length) throw fail(`the function has symbols other than ${x} (${extra.join(", ")})`);
  const n = "n", nS = S(n);
  const bps = breakpoints(f0, x, -Ln, Ln);
  const exactCuts = [X.neg(L), ...bps.map(([, r]) => r), L];
  const coefficient = (kernel) => {
    let total = X.ZERO;
    for (let i = 0; i + 1 < exactCuts.length; i++) {
      const a = exactCuts[i], b = exactCuts[i + 1];
      const mid = (numOf(a) + numOf(b)) / 2;
      const piece = restrict(f0, x, mid);
      if (piece === X.UNDEF || X.contains(piece, X.UNDEF)) throw fail("the function is not defined on part of the interval");
      let r;
      try { r = definiteIntegral(C(X.mul(piece, kernel)), x, a, b, {}); } catch (e) { if (e && e.code === "TIMEOUT") throw e; throw fail(`a Fourier coefficient integral could not be evaluated${e && e.message ? ` (${e.message})` : ""}`); }
      if (!r || r.status !== "exact") throw fail("a Fourier coefficient has no closed form Quelvra can derive");
      total = X.add(total, r.value);
    }
    return C(X.div(total, L));
  };
  const arg = C(X.div(X.mul(nS, X.PI, S(x)), L));
  const a0 = nice(coefficient(X.ONE));
  let an = coefficient(X.fn("cos", arg)), bn = coefficient(X.fn("sin", arg));
  an = nice(integerTrig(an, n)); bn = nice(integerTrig(bn, n));
  for (const [lab, c] of [["an", an], ["bn", bn]]) {
    for (let k = 1; k <= 8; k++) { const v = numOf(C(X.subs(c, { n: X.num(k) }))); if (!Number.isFinite(v)) throw fail(`the general formula for ${lab} breaks down at n = ${k}; that coefficient needs a separate computation (not supported)`); }
  }
  env.log.add({ rule: "fourier.coefficients", title: "Fourier coefficients", why: `a_n = (1/L) integral of f cos(n pi x/L), b_n = (1/L) integral of f sin(n pi x/L) over [-L, L] with L = ${toText(L)}; sin(n pi) = 0 and cos(n pi) = (-1)^n for integer n.`, before: f0, after: X.tuple(a0, an, bn) });
  const series = C(X.add(C(X.div(a0, X.TWO)), X.sum(C(X.add(X.mul(an, X.fn("cos", arg)), X.mul(bn, X.fn("sin", arg)))), nS, X.ONE, X.OO)));
  const fe = envFn(f0);
  const cutsN = exactCuts.map(numOf);
  const numCoef = (kern) => { let s = 0, err = 0; for (let i = 0; i + 1 < cutsN.length; i++) { const r = quad1((u) => fe({ [x]: u }) * kern(u), cutsN[i], cutsN[i + 1], { m: 16, panels: 8 }); if (!r.ok) return { ok: false }; s += r.value; err += r.err; } return { ok: true, value: s / Ln, err: err / Ln }; };
  return {
    answers: [
      { kind: "exact", label: "a0", tree: a0 }, { kind: "exact", label: "an", tree: an }, { kind: "exact", label: "bn", tree: bn },
      { kind: "exact", label: "Fourier series", tree: series, note: "a0/2 + sum over n >= 1 of (an cos(n pi x/L) + bn sin(n pi x/L))" },
    ],
    verify: () => {
      const checks = [];
      const cmp = (lab, claimed, ref) => {
        if (!ref.ok) return open("quadrature", `the numeric ${lab} did not converge`);
        return Math.abs(claimed - ref.value) <= Math.max(1e-8, 20 * ref.err) ? null : bad("quadrature", `${lab}: numeric quadrature gives ${fmt(ref.value)}, the formula gives ${fmt(claimed)}`);
      };
      const r0 = cmp("a0", numOf(a0), numCoef(() => 1));
      if (r0) return TCV([r0]);
      for (let k = 1; k <= 8; k++) {
        const w = (k * Math.PI) / Ln;
        const ra = cmp(`a${k}`, numOf(C(X.subs(an, { n: X.num(k) }))), numCoef((u) => Math.cos(w * u)));
        if (ra) return TCV([ra]);
        const rb = cmp(`b${k}`, numOf(C(X.subs(bn, { n: X.num(k) }))), numCoef((u) => Math.sin(w * u)));
        if (rb) return TCV([rb]);
      }
      checks.push(pass("quadrature", "a0 and a_n, b_n for n = 1..8 agree with Gauss-Legendre quadrature of f (split at its breakpoints)"));
      return TCV(checks);
    },
  };
}
// ------------------------------------------------------------------ Fourier transform
// F(w) = integral f(t) e^(-i w t) dt over the real line
function ftTable(f, t, w) {
  const T = S(t), W = S(w);
  // constant multiple
  let c = X.ONE, core = f;
  if (f.k === "mul") { const cs = f.args.filter((a) => !X.hasSym(a, t)); if (cs.length) { c = C(X.mul(...cs)); core = C(X.mul(...f.args.filter((a) => X.hasSym(a, t)))); } }
  const pos = (u) => { const v = numOf(u); return Number.isFinite(v) && v > 0 && !X.freeSymbols(u).size; };
  // e^(u)
  if (core.k === "pow" && core.args[0] === X.E) {
    const u = core.args[1];
    const a1 = C(X.div(X.neg(u), X.fn("abs", T)));
    if (!X.hasSym(a1, t) && pos(a1)) return { F: X.mul(c, X.TWO, a1, X.recip(X.add(X.pow(a1, X.TWO), X.pow(W, X.TWO)))), rule: "e^(-a|t|) -> 2a/(a^2 + w^2)" };
    const a2 = C(X.div(X.neg(u), X.pow(T, X.TWO)));
    if (!X.hasSym(a2, t) && pos(a2)) return { F: X.mul(c, X.sqrt(X.div(X.PI, a2)), E_(X.neg(X.div(X.pow(W, X.TWO), X.mul(X.num(4), a2))))), rule: "e^(-a t^2) -> sqrt(pi/a) e^(-w^2/(4a))" };
    return null;
  }
  // c / (t^2 + a^2)
  if (core.k === "pow" && X.isInt(core.args[1]) && core.args[1].v.n === -1n) {
    const q = P.fromTree(C(expand(core.args[0], ctx())), t);
    if (q && q.length === 3 && N.isZero(q[1])) {
      const lead = q[2], a2 = N.div(q[0], lead);
      if (N.sign(a2) > 0 && N.sign(lead) > 0) { const a = C(X.sqrt(X.num(a2))); return { F: X.mul(c, X.recip(X.num(lead)), X.PI, X.recip(a), E_(X.neg(X.mul(a, X.fn("abs", W))))), rule: "1/(t^2 + a^2) -> (pi/a) e^(-a|w|)" }; }
    }
    return null;
  }
  // rectangular pulse piecewise(1, |t| <= a, 0, otherwise)
  if (core.k === "piecewise" && core.args.length === 4) {
    const [v1, c1, v2] = core.args;
    if (X.hasSym(v1, t) || !X.isZero(C(v2))) return null;
    if (c1.k === "rel" && (c1.op === "<=" || c1.op === "<") && c1.args[0].k === "fn" && c1.args[0].name === "abs" && c1.args[0].args[0] === T && pos(c1.args[1])) {
      const a = c1.args[1];
      return { F: X.mul(c, v1, X.TWO, X.fn("sin", X.mul(a, W)), X.recip(W)), rule: "rect: 1 for |t| <= a -> 2 sin(a w)/w" };
    }
    return null;
  }
  return null;
}
// integral over [0, oo) of g(t) trig(w t) dt: half-period panels plus repeated averaging
function oscIntegral(g, w, trig, breaks) {
  const half = Math.PI / Math.abs(w);
  const sums = [];
  let acc = 0;
  const cuts = (a, b) => [a, ...breaks.filter((p) => p > a && p < b), b];
  for (let k = 0; k < 160; k++) {
    const a = k * half, b = (k + 1) * half;
    const cs = cuts(a, b);
    for (let i = 0; i + 1 < cs.length; i++) { const v = glPanel((u) => g(u) * trig(w * u), cs[i], cs[i + 1], 20, 2); if (!Number.isFinite(v)) return { ok: false }; acc += v; }
    sums.push(acc);
  }
  // repeated averaging (Euler transform) of the last partial sums
  let row = sums.slice(-24);
  while (row.length > 1) row = row.slice(1).map((v, i) => (v + row[i]) / 2);
  const last = sums.slice(-25, -1);
  let row2 = last;
  while (row2.length > 1) row2 = row2.slice(1).map((v, i) => (v + row2[i]) / 2);
  return { ok: true, value: row[0], err: Math.abs(row[0] - row2[0]) + 1e-13 };
}
function cmdFourierTransform(node, env) {
  const f = node.args[0];
  if (!f || ["eq", "vector", "tuple", "matrix"].includes(f.k)) throw fail("fouriertransform(f(t)) needs a function of t");
  const t = node.args[1] && node.args[1].k === "sym" ? node.args[1].name : "t";
  const w = node.args[2] && node.args[2].k === "sym" ? node.args[2].name : "w";
  const extra = [...X.freeSymbols(f)].filter((v) => v !== t);
  if (extra.length) throw fail(`the function has symbols other than ${t}`);
  const hit = ftTable(C(f), t, w);
  if (!hit) throw fail("no Fourier transform rule applies (supported: e^(-a|t|), e^(-a t^2), 1/(t^2 + a^2) and rectangular pulses, times constants); functions that are not absolutely integrable are refused");
  const F = nice(hit.F);
  env.log.add({ rule: "fourier.transform", title: "Fourier transform from the table", why: `Convention F(w) = integral of f(t) e^(-i w t) dt; ${hit.rule}.`, before: f, after: F });
  const fe = envFn(f);
  const bps = breakpoints(C(f), t, 0, 1e6).map(([v]) => v);
  return {
    answers: [{ kind: "exact", label: "Fourier transform", tree: F, note: "F(w) = integral of f(t) e^(-i w t) dt" }],
    verify: () => {
      const checks = [];
      for (const w0 of [0.7, 1.3, 2.9]) {
        const even = (u) => fe({ [t]: u }) + fe({ [t]: -u }), odd = (u) => fe({ [t]: u }) - fe({ [t]: -u });
        const re = oscIntegral(even, w0, Math.cos, bps), im = oscIntegral(odd, w0, Math.sin, bps);
        const want = evalZ(forEval(F), { [w]: w0 });
        if (!re.ok || !im.ok || !want) { checks.push(open("numeric-transform", `no numeric value at w = ${w0}`)); continue; }
        const refRe = re.value, refIm = -im.value;
        const tol = Math.max(1e-7, 50 * (re.err + im.err));
        if (tol > 1e-4) { checks.push(open("numeric-transform", "the numeric Fourier integral is not accurate enough")); continue; }
        checks.push(Math.abs(want.re - refRe) <= tol * Math.max(1, Math.abs(refRe)) && Math.abs(want.im - refIm) <= tol * Math.max(1, Math.abs(refRe)) ? pass("numeric-transform", `the Fourier integral at w = ${w0} is ${fmtC({ re: refRe, im: refIm })} numerically`) : bad("numeric-transform", `at w = ${w0} the numeric Fourier integral is ${fmtC({ re: refRe, im: refIm })}, the formula gives ${fmtC(want)}`));
      }
      return TCV(checks);
    },
  };
}

// ------------------------------------------------------------------ Z-transform
// Z{n^m r^n} = (-z d/dz)^m z/(z - r)
function cmdZtransform(node, env) {
  const f = node.args[0];
  if (!f || ["eq", "vector", "tuple", "matrix"].includes(f.k)) throw fail("ztransform(f(n)) needs a sequence f(n)");
  const n = node.args[1] && node.args[1].k === "sym" ? node.args[1].name : "n";
  const z = node.args[2] && node.args[2].k === "sym" ? node.args[2].name : "z";
  const extra = [...X.freeSymbols(f)].filter((v) => v !== n);
  if (extra.length) throw fail(`the sequence has symbols other than ${n}`);
  const terms = expTerms(f, n);
  if (!terms) throw fail("no Z-transform rule applies (supported: sums of n^m r^n, including cos / sin of linear arguments)");
  const Z = S(z);
  const parts = [];
  let R = 0;
  for (const { coef, n: m, k } of terms) {
    const r = C(E_(k));
    const rv = cnumOf(r);
    if (!rv) throw fail("unsupported sequence");
    R = Math.max(R, Math.hypot(rv.re, rv.im));
    let g = X.div(Z, X.sub(Z, r));
    for (let j = 0; j < m; j++) g = C(X.mul(X.NEG_ONE, Z, D(g, z)));
    parts.push(X.mul(coef, g));
  }
  const F = realForm(X.add(...parts), z);
  if (!F) throw fail("the transform could not be brought to a real form");
  env.log.add({ rule: "z.table", title: "Z-transform term by term", why: "Z{r^n} = z/(z - r) and multiplying by n applies -z d/dz; cos and sin are written as complex exponentials.", before: f, after: F });
  const fe = envFn(f);
  return {
    answers: [{ kind: "exact", label: "Z-transform", tree: F, note: `converges for |z| > ${fmt(R)}` }],
    verify: () => {
      const checks = [];
      for (const z0 of [R + 1.7, R + 3.1, -(R + 2.3)]) {
        let s = 0, ok = true, k = 0;
        for (; k < 5000; k++) { const term = fe({ [n]: k }) * Math.pow(z0, -k); if (!Number.isFinite(term)) { ok = false; break; } s += term; if (k > 20 && Math.abs(term) < 1e-17 * Math.max(1, Math.abs(s))) break; }
        const want = evalR(forEval(F), { [z]: z0 });
        if (!ok || !Number.isFinite(want)) { checks.push(open("partial-sums", `no numeric value at z = ${fmt(z0)}`)); continue; }
        checks.push(closeTo(want, s, 1e-9) ? pass("partial-sums", `sum of f(n) z^(-n) at z = ${fmt(z0)} is ${fmt(s)} (${k} terms)`) : bad("partial-sums", `at z = ${fmt(z0)} the series sums to ${fmt(s)}, not ${fmt(want)}`));
      }
      return TCV(checks);
    },
  };
}

export { breakpoints, restrict, integerTrig };
export const TRANSFORMS = { laplace: cmdLaplace, invlaplace: cmdInvLaplace, lapsolve: cmdLapsolve, fourier: cmdFourier, fouriertransform: cmdFourierTransform, ztransform: cmdZtransform };
export { laplaceCore, realForm, expTerms, linearIn, oscIntegral };
void ID; void numerDenom; void fmtC; void quadHalfLine;
