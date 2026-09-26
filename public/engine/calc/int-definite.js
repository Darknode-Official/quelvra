// Definite and improper integrals.
//
//   definiteIntegral(f, x, a, b, {steps, pv, digits, timeLimit}) ->
//     { status: "exact", value, approx, F, method, conditions, checks }
//     { status: "diverges", reason, F }
//     { status: "approx", value (number), record (numeric.js Approx record), reason }
//     throws { code: "UNSUPPORTED" | "NOTREAL" }
//
// Method (never FTC across a discontinuity):
//   1. find an antiderivative F (calc/integrate.js; independently verified there)
//   2. collect every point of [a, b] where f or F can break: zeros of denominators and of radicands,
//      logarithm / Ei / Ci / li arguments, poles of tan, sec, cot, csc (including the tan(u/2) of a
//      Weierstrass substitution), domain edges of asin / acos
//   3. split [a, b] at those points; on each open piece F' = f, so the piece contributes
//      lim F(q-) - lim F(p+) (one-sided limits, calc/limit.js + special-function limits); an infinite or
//      non-existent limit proves that the integral diverges (a principal value is formed only on request)
//   4. cross-check: each piece numerically against F(t) - F(s) on an interior sub-interval (catches a missed
//      jump of F), and the whole value against numeric.js quadrature when that converges. Any disagreement
//      withdraws the exact answer; a converged numeric value is then returned as an approximation.
//   5. no antiderivative: numeric quadrature, returned as an approximation only.

import * as X from "../expr.js";
import { toText } from "../print.js";
import { StepLog, NO_STEPS } from "../steps.js";
import * as P from "../poly.js";
import * as NUM from "../numeric.js";
import { integrate, intError } from "./integrate.js";
import { canon, evalD, linearCoeffs } from "./int-util.js";
import { lim, isInf, isNegInf, NEG_OO, limText } from "./int-limit.js";

const { ZERO, ONE, PI, OO } = X;
const T = (u) => toText(u);

// ---------------------------------------------------------------- numeric helpers
const GK_X = [0.991455371120812639, 0.949107912342758525, 0.864864423359769073, 0.741531185599394440, 0.586087235467691130, 0.405845151377397167, 0.207784955007898468, 0];
const GK_W = [0.022935322010529225, 0.063092092629978553, 0.104790010322250184, 0.140653259715525919, 0.169004726639267903, 0.190350578064785410, 0.204432940075298892, 0.209482141084727828];
const G_W = [0.129484966168869693, 0.279705391489276668, 0.381830050505118945, 0.417959183673469388];
function gk(f, a, b) {
  const c = (a + b) / 2, h = (b - a) / 2;
  let k = GK_W[7] * f(c), g = G_W[3] * f(c);
  for (let i = 0; i < 7; i++) {
    const d = h * GK_X[i];
    const s = f(c - d) + f(c + d);
    k += GK_W[i] * s;
    if (i % 2 === 1) g += G_W[(i - 1) / 2] * s;
  }
  return { v: k * h, e: Math.abs((k - g) * h) };
}
// adaptive Gauss-Kronrod on a finite interval with a function that may return NaN (-> failure)
export function quad(f, a, b, tol = 1e-10, maxSeg = 2000) {
  let segs = [{ a, b, ...gk(f, a, b) }];
  for (let it = 0; it < maxSeg; it++) {
    let tot = 0, err = 0, wi = 0;
    for (let i = 0; i < segs.length; i++) { tot += segs[i].v; err += segs[i].e; if (segs[i].e > segs[wi].e) wi = i; }
    if (!Number.isFinite(tot)) return { value: NaN, err: Infinity, ok: false };
    if (err <= tol * Math.max(1, Math.abs(tot))) return { value: tot, err, ok: true };
    const s = segs[wi], m = (s.a + s.b) / 2;
    segs.splice(wi, 1, { a: s.a, b: m, ...gk(f, s.a, m) }, { a: m, b: s.b, ...gk(f, m, s.b) });
  }
  let tot = 0, err = 0;
  for (const s of segs) { tot += s.v; err += s.e; }
  return { value: tot, err, ok: Number.isFinite(tot) && err <= 1e-6 * Math.max(1, Math.abs(tot)) };
}

// independent quadrature of f over [a, b] (trees; +-oo allowed) with the integrator's own evaluator
export function independentQuad(f, x, a, b) {
  const av = valOf(a), bv = valOf(b);
  const fx = (t) => evalD(f, { [x.name]: t });
  const safe = (g) => (t) => { const v = g(t); return Number.isFinite(v) ? v : NaN; };
  let g, lo = 0, hi = 1;
  if (Number.isFinite(av) && Number.isFinite(bv)) { g = fx; lo = av; hi = bv; }
  else if (Number.isFinite(av)) g = (t) => fx(av + t / (1 - t)) / ((1 - t) * (1 - t));
  else if (Number.isFinite(bv)) g = (t) => fx(bv - t / (1 - t)) / ((1 - t) * (1 - t));
  else { lo = -1; g = (t) => fx(t / (1 - t * t)) * (1 + t * t) / ((1 - t * t) * (1 - t * t)); }
  // Gauss-Kronrod nodes never touch the endpoints, so endpoint singularities of integrable type are fine
  const r = quad(safe(g), lo, hi, 1e-11, 4000);
  return r;
}

const valOf = (u) => (typeof u === "number" ? u : u.k === "__num" ? u.v : u === OO ? Infinity : isNegInf(u) ? -Infinity : evalD(u));

// ---------------------------------------------------------------- break points
const TRIG_POLE = { tan: "cos", sec: "cos", cot: "sin", csc: "sin" };

// real zeros of g in [lo, hi] (numbers): { pts: [{t, v}], exact }
function zerosOf(g, x, lo, hi) {
  g = canon(g);
  if (X.freeOf(g, x)) return { pts: [], exact: true };
  // sin / cos of a linear argument: periodic zeros
  if (g.k === "fn" && (g.name === "sin" || g.name === "cos")) {
    const L = g.args[0] === x ? [ONE, ZERO] : linearCoeffs(g.args[0], x);
    if (!L) return { pts: [], exact: false };
    if (!Number.isFinite(lo) || !Number.isFinite(hi)) return { pts: [], exact: false, periodic: true };
    const p = evalD(L[0]), q = evalD(L[1]);
    if (!Number.isFinite(p) || !Number.isFinite(q) || p === 0) return { pts: [], exact: false };
    // p x + q = off + n pi
    const off = g.name === "cos" ? Math.PI / 2 : 0;
    const n1 = Math.ceil((Math.min(p * lo, p * hi) + q - off) / Math.PI - 1e-9), n2 = Math.floor((Math.max(p * lo, p * hi) + q - off) / Math.PI + 1e-9);
    if (n2 - n1 > 200) return { pts: [], exact: false };
    const pts = [];
    for (let n = n1; n <= n2; n++) {
      const t = canon(X.div(X.sub(X.add(g.name === "cos" ? X.mul(X.HALF, PI) : ZERO, X.mul(X.num(n), PI)), L[1]), L[0]));
      const v = evalD(t);
      if (v >= lo - 1e-12 && v <= hi + 1e-12) pts.push({ t, v });
    }
    return { pts, exact: true };
  }
  if (g.k === "fn" && g.name === "abs") return zerosOf(g.args[0], x, lo, hi);
  if (g.k === "fn" && g.args.length === 1) {
    // monotone functions vanishing only at 0, and ln (vanishing only at 1)
    if (["atan", "asinh", "sinh", "tanh", "asin", "erf", "erfi", "sign", "cbrt"].includes(g.name)) return zerosOf(g.args[0], x, lo, hi);
    if (g.name === "ln") return zerosOf(X.sub(g.args[0], ONE), x, lo, hi);
    if (g.name === "cosh") return { pts: [], exact: true };
  }
  if (g.k === "pow" && X.isNum(g.args[1]) && g.args[1].v.n > 0n) return zerosOf(g.args[0], x, lo, hi);
  if (g.k === "mul") {
    const out = { pts: [], exact: true };
    for (const a of g.args) { const r = zerosOf(a, x, lo, hi); out.pts.push(...r.pts); if (!r.exact) out.exact = false; if (r.periodic) out.periodic = true; }
    return out;
  }
  if (g.k === "pow" && g.args[0] === X.E) return { pts: [], exact: true }; // e^u > 0
  const [n] = P.numDen(g);
  let isPoly = false;
  try { isPoly = !!P.fromTree(n, x.name); } catch (e) { if (!e || e.code !== "BUDGET") throw e; }
  if (isPoly) {
    let sol;
    try { sol = P.solvePolynomial(n, x.name); } catch (e) { if (e && e.code) return { pts: [], exact: false }; throw e; }
    const pts = [];
    for (const r of sol.exact || []) {
      if (!r.real) continue;
      const v = evalD(r.root);
      if (v >= lo - 1e-12 && v <= hi + 1e-12) pts.push({ t: r.root, v });
    }
    let exact = true;
    if (!sol.complete) for (const r of sol.approx || []) if (r.im === null || r.im === undefined || r.im === 0) { const v = Number(r.re); if (v >= lo - 1e-9 && v <= hi + 1e-9) exact = false; }
    return { pts, exact };
  }
  // general: numeric scan with identification of the root
  const L0 = Number.isFinite(lo) ? lo : (Number.isFinite(hi) ? hi - 200 : -200), H0 = Number.isFinite(hi) ? hi : L0 + 200;
  const M = 4000, pts = [];
  let exact = true;
  const gv = (t) => evalD(g, { [x.name]: t });
  let prev = gv(L0), prevT = L0;
  for (let i = 1; i <= M; i++) {
    const t = L0 + ((H0 - L0) * i) / M, v = gv(t);
    if (Number.isFinite(prev) && Number.isFinite(v) && (prev === 0 || prev * v < 0 || (Math.abs(v) < 1e-9))) {
      let A = prevT, Bv = t, fa = prev;
      if (fa !== 0) for (let k = 0; k < 80; k++) { const m = (A + Bv) / 2, fm = gv(m); if (fm === 0) { A = Bv = m; break; } if (fa * fm < 0) Bv = m; else { A = m; fa = fm; } }
      const r = (A + Bv) / 2;
      const id = identify(r, g, x);
      if (id) { if (!pts.some((p) => Math.abs(p.v - r) < 1e-9)) pts.push({ t: id, v: evalD(id) }); } else exact = false;
    }
    prev = v; prevT = t;
  }
  if (!Number.isFinite(lo) || !Number.isFinite(hi)) exact = false; // scan cannot cover an infinite range
  return { pts, exact };
}
// identify a numeric root r of g as a simple closed form, verified exactly
function identify(r, g, x) {
  const cands = [];
  for (let d = 1; d <= 12; d++) {
    const n = Math.round(r * d);
    if (Math.abs(n / d - r) < 1e-9) cands.push(X.num(n, d));
    const np = Math.round((r / Math.PI) * d);
    if (Math.abs((np / d) * Math.PI - r) < 1e-9) cands.push(canon(X.mul(X.num(np, d), PI)));
  }
  if (r > 0) { const l = Math.round(Math.exp(r)); if (Math.abs(Math.log(l) - r) < 1e-9 && l > 0) cands.push(X.fn("ln", X.num(l))); }
  for (const c of cands) {
    try { if (canon(X.subs(g, { [x.name]: c })) === ZERO) return c; } catch (e) { if (!e || !e.code) throw e; }
  }
  return null;
}

// every point where u (f or F) can fail to be continuous / defined
function breakPoints(u, x, lo, hi) {
  const out = { pts: [], exact: true, periodic: false };
  const add = (r) => { for (const p of r.pts) if (!out.pts.some((q) => Math.abs(q.v - p.v) < 1e-12 * Math.max(1, Math.abs(p.v)))) out.pts.push(p); if (!r.exact) out.exact = false; if (r.periodic) out.periodic = true; };
  const walk = (w) => {
    if (X.freeOf(w, x)) return;
    for (const a of w.args) walk(a);
    if (w.k === "pow") {
      const [b, e] = w.args;
      if (X.freeOf(b, x)) return;
      if (!X.isNum(e) || e.v.n < 0n || e.v.d !== 1n) add(zerosOf(b, x, lo, hi));
    } else if (w.k === "fn") {
      const g = w.args[0];
      if (!g || X.freeOf(g, x)) return;
      if (["ln", "log", "Ei", "Ci", "Chi"].includes(w.name)) add(zerosOf(g, x, lo, hi));
      else if (w.name === "li") { add(zerosOf(g, x, lo, hi)); add(zerosOf(X.sub(g, ONE), x, lo, hi)); }
      else if (TRIG_POLE[w.name]) add(zerosOf(X.fn(TRIG_POLE[w.name], g), x, lo, hi));
      else if (["asin", "acos", "atanh", "acoth", "asec", "acsc"].includes(w.name)) { add(zerosOf(X.sub(g, ONE), x, lo, hi)); add(zerosOf(X.add(g, ONE), x, lo, hi)); }
      else if (["sinh", "cosh", "tanh", "sin", "cos", "atan", "acot", "abs", "exp", "erf", "erfi", "Si", "Shi", "FresnelS", "FresnelC", "asinh", "sign", "acosh"].includes(w.name)) { /* continuous */ }
      else out.exact = false; // unknown function: no exact claim
    }
  };
  walk(u);
  return out;
}

// integrand real on (lo, hi)? (sampled; isolated undefined points are allowed)
function realOnInterval(f, x, lo, hi) {
  const map = (s) => (Number.isFinite(lo) && Number.isFinite(hi) ? lo + (hi - lo) * s : Number.isFinite(lo) ? lo + s / (1 - s) : Number.isFinite(hi) ? hi - (1 - s) / s : Math.tan(Math.PI * (s - 0.5)));
  let bad = 0, run = 0, maxRun = 0;
  const M = 997;
  for (let i = 1; i < M; i++) {
    const env = { [x.name]: map(i / M) };
    const v = evalD(f, env);
    // NaN from an overflow (e.g. e^(x^2) / e^(2x^2) far out) is not evidence of a non-real value
    if (Number.isNaN(v) && !overflowed(f, env)) { bad++; run++; maxRun = Math.max(maxRun, run); } else run = 0;
  }
  return maxRun < 3 && bad < 6;
}

function overflowed(u, env) {
  const v = evalD(u, env);
  if (v === Infinity || v === -Infinity) return true;
  return u.args.some((a) => overflowed(a, env));
}

function numericWhole(f, x, a, b, digits) {
  try {
    const r = NUM.integrate(f, x.name, a, b, { digits });
    if (r && r.value !== "undefined") return { rec: r, value: Number(r.value), err: Number(r.errorBound), converged: !!r.converged };
    return { rec: r, value: NaN, converged: false, diverges: r && r.warnings && r.warnings.some((w) => /diverge|not integrable/i.test(w)) };
  } catch (e) {
    if (e && e.code) return null; // the numeric compiler does not know a function (e.g. Si)
    throw e;
  }
}

// quadrature split at the singular points of f and at 0 for (-oo, oo): every piece must converge on its
// own, so a divergent integral cannot "converge" by cancellation between pieces
function splitPoints(f, x, av, bv) {
  const pts = [];
  try {
    const bp = breakPoints(f, x, av, bv);
    for (const p of bp.pts) if (p.v > av && p.v < bv) pts.push(p.v);
  } catch (e) { if (!e || !e.code) throw e; }
  if (av === -Infinity && bv === Infinity && !pts.length) pts.push(0);
  return [...new Set(pts)].sort((p, q) => p - q);
}
function numericSplit(f, x, a, b, digits) {
  const av = valOf(a), bv = valOf(b);
  const pts = splitPoints(f, x, av, bv);
  if (!pts.length) return numericWhole(f, x, a, b, digits);
  const nodes = [av === -Infinity ? "-oo" : av === Infinity ? "oo" : a, ...pts, bv === Infinity ? "oo" : bv === -Infinity ? "-oo" : b];
  let value = 0, err = 0, dmin = Infinity;
  const recs = [];
  for (let i = 0; i + 1 < nodes.length; i++) {
    const r = numericWhole(f, x, nodes[i], nodes[i + 1], digits);
    if (!r) return null;
    if (!r.converged || !Number.isFinite(r.value)) return { rec: r.rec, value: NaN, converged: false, diverges: r.diverges };
    value += r.value; err += Number.isFinite(r.err) ? r.err : 0; dmin = Math.min(dmin, r.rec.digits);
    recs.push(r.rec);
  }
  const dg = Math.max(1, Math.min(dmin, 15));
  const rec = { value: String(+value.toPrecision(dg)), digits: dg, requested: digits, errorBound: err.toExponential(1), method: `${recs[0].method}, split at ${pts.map((v) => +v.toPrecision(8)).join(", ")}`, iterations: recs.reduce((s2, r) => s2 + (r.iterations || 0), 0), converged: true, warnings: [] };
  return { rec, value, err, converged: true };
}
function quadSplit(f, x, a, b) {
  const av = valOf(a), bv = valOf(b);
  const pts = splitPoints(f, x, av, bv);
  const nodes = [av, ...pts, bv];
  let value = 0, err = 0;
  for (let i = 0; i + 1 < nodes.length; i++) {
    const asTree = (v) => (v === Infinity ? OO : v === -Infinity ? NEG_OO : numTree(v));
    const r = independentQuad(f, x, asTree(nodes[i]), asTree(nodes[i + 1]));
    if (!r.ok) return { ok: false, value: NaN, err: Infinity };
    value += r.value; err += r.err;
  }
  return { ok: true, value, err };
}
// a finite double as a tree for the quadrature helpers (only its numeric value is used)
const numTree = (v) => ({ k: "__num", v, args: [] });

// ---------------------------------------------------------------- main
export function definiteIntegral(f, x, a, b, opts = {}) {
  const xs = typeof x === "string" ? X.sym(x) : x;
  const log = opts.steps || NO_STEPS;
  const f0 = canon(f);
  a = canon(a); b = canon(b);
  const digits = opts.digits || 12;
  if (a === b) return { status: "exact", value: ZERO, approx: 0, F: null, method: "int.ftc", conditions: [], checks: ["empty interval"] };
  const params = [...X.freeSymbols(f0)].filter((n) => n !== xs.name);
  const bParams = [...X.freeSymbols(a), ...X.freeSymbols(b)];
  if (params.length || bParams.length) return symbolicDefinite(f0, xs, a, b, opts, log);
  let av = valOf(a), bv = valOf(b);
  if (Number.isNaN(av) || Number.isNaN(bv)) throw intError("UNSUPPORTED", "The limits of integration must be real numbers or +-oo.");
  if (av > bv) {
    const r = definiteIntegral(f0, xs, b, a, opts);
    if (r.status === "exact") return { ...r, value: canon(X.neg(r.value)), approx: -r.approx, checks: [...r.checks, "reversed limits: int_a^b = -int_b^a"] };
    if (r.status === "approx") return { ...r, value: -r.value };
    return r;
  }
  if (!realOnInterval(f0, xs, av, bv)) throw intError("NOTREAL", `The integrand ${T(f0)} is not real-valued on part of the interval [${T(a)}, ${T(b)}], so the real integral is not defined there.`);

  const fallback = (why, numRes) => {
    const nr = numRes || numericSplit(f0, xs, a, b, digits);
    if (nr && nr.converged && Number.isFinite(nr.value)) return { status: "approx", value: nr.value, record: nr.rec, reason: why };
    // second quadrature (own evaluator, knows the special functions); reported as such
    const q = quadSplit(f0, xs, a, b);
    if (q.ok && Number.isFinite(q.value) && q.err <= 1e-9 * Math.max(1, Math.abs(q.value))) {
      const absErr = Math.max(q.err, 1e-15 * Math.max(1, Math.abs(q.value)));
      const tiny = Math.abs(q.value) <= 10 * absErr;
      const dg = tiny ? 0 : Math.max(1, Math.min(12, Math.floor(-Math.log10(absErr / Math.abs(q.value)))));
      const shown = tiny ? "0" : String(+q.value.toPrecision(dg));
      const rec = { value: shown, digits: dg, requested: digits, errorBound: (tiny ? Math.max(absErr, Math.abs(q.value)) * 2 : absErr + 0.5 * 10 ** (Math.floor(Math.log10(Math.abs(q.value))) - dg + 1)).toExponential(1), method: "adaptive Gauss-Kronrod (Quelvra integrator)", iterations: 0, converged: true, warnings: ["numeric.js quadrature did not converge; this value comes from the integrator's own adaptive quadrature and has no second independent check"] };
      return { status: "approx", value: q.value, record: rec, reason: why, singleMethod: true };
    }
    if (nr && nr.diverges) throw intError("UNSUPPORTED", `${why} Numerical quadrature also fails to converge (the integral appears to diverge), but that is not a proof.`, { numeric: nr && nr.rec });
    throw intError("UNSUPPORTED", `${why} Numerical quadrature did not converge either.`, { numeric: nr && nr.rec });
  };

  // 1. antiderivative
  let anti = null;
  try { anti = integrate(f0, xs, { steps: new StepLog(), timeLimit: opts.timeLimit || 6000 }); } catch (e) {
    if (!e || !e.code) throw e;
    const why = e.code === "NONELEMENTARY" ? "The antiderivative is not elementary, so the value is computed numerically." : "No verified antiderivative was found, so the value is computed numerically.";
    const r = fallback(why);
    if (e.code === "NONELEMENTARY") r.nonelementary = e.message;
    return r;
  }
  const F = anti.F;
  // 2. break points of f and F
  const bf = breakPoints(f0, xs, av, bv), bF = breakPoints(F, xs, av, bv);
  if (!bf.exact || !bF.exact) return fallback(bf.periodic || bF.periodic ? "The antiderivative has infinitely many discontinuities on this range, so the value is computed numerically." : "The points where the integrand or antiderivative break could not all be located exactly, so the value is computed numerically.");
  const all = [...bf.pts];
  for (const p of bF.pts) if (!all.some((q) => Math.abs(q.v - p.v) < 1e-12 * Math.max(1, Math.abs(p.v)))) all.push(p);
  const interior = all.filter((p) => p.v > av && p.v < bv).sort((p, q) => p.v - q.v);
  const fSing = (p) => bf.pts.some((q) => Math.abs(q.v - p.v) < 1e-12 * Math.max(1, Math.abs(p.v)));
  const nodes = [{ t: a, v: av }, ...interior, { t: b, v: bv }];

  log.add({ rule: "int.ftc", title: "Antiderivative", why: `An antiderivative (verified by differentiation) is F(${xs.name}) = ${T(F)}.`, before: X.integral(f0, xs), after: F });
  if (interior.length) {
    const sing = interior.filter(fSing), jump = interior.filter((p) => !fSing(p));
    const parts = [];
    if (sing.length) parts.push(`the integrand is undefined or unbounded at ${xs.name} = ${sing.map((p) => T(p.t)).join(", ")}`);
    if (jump.length) parts.push(`the antiderivative is discontinuous (or undefined) at ${xs.name} = ${jump.map((p) => T(p.t)).join(", ")}`);
    log.add({ rule: "int.improper", title: "Split the interval", why: `The fundamental theorem of calculus needs F continuous on the whole interval, but ${parts.join(" and ")}. Split there and use one-sided limits on each piece.`, before: X.integral(f0, xs, a, b), after: X.add(...nodes.slice(1).map((n, i) => X.integral(f0, xs, nodes[i].t, n.t))) });
  }

  // 3. one-sided limits on each piece
  const pieces = [];
  let divergent = null;
  for (let i = 0; i + 1 < nodes.length; i++) {
    const p = nodes[i], q = nodes[i + 1];
    const Lp = isInf(p.t) ? lim(F, xs, p.t, "") : endValue(F, xs, p, "+", all);
    const Lq = isInf(q.t) ? lim(F, xs, q.t, "") : endValue(F, xs, q, "-", all);
    pieces.push({ p, q, Lp, Lq });
    for (const [Lr, pt, side] of [[Lp, p, "+"], [Lq, q, "-"]]) {
      if (Lr.k === "unknown") return fallback(`A one-sided limit of the antiderivative at ${T(pt.t)} could not be determined (${Lr.reason}).`);
      if ((Lr.k === "inf" || Lr.k === "dne") && !divergent) divergent = { pt, side, Lr, piece: pieces.length - 1 };
    }
  }

  // 4a. piece checks: numeric integral over an interior sub-interval against F(t) - F(s)
  const checks = [];
  const fx = (t) => evalD(f0, { [xs.name]: t });
  const Fx = (t) => evalD(F, { [xs.name]: t });
  for (const pc of pieces) {
    const pv = pc.p.v, qv = pc.q.v;
    let s, t;
    if (Number.isFinite(pv) && Number.isFinite(qv)) { s = pv + (qv - pv) * 1e-3; t = qv - (qv - pv) * 1e-3; }
    else if (Number.isFinite(pv)) { s = pv + 1e-3; t = pv + 25; }
    else if (Number.isFinite(qv)) { t = qv - 1e-3; s = qv - 25; }
    else { s = -25; t = 25; }
    const nq = quad(fx, s, t);
    const dF = Fx(t) - Fx(s);
    if (!nq.ok || !Number.isFinite(dF)) return fallback("The antiderivative could not be cross-checked numerically on this interval.");
    const tolP = 1e-7 * Math.max(1, Math.abs(dF)) + 10 * nq.err;
    if (Math.abs(nq.value - dF) > tolP) return fallback(`The antiderivative disagreed with numerical integration on [${s.toPrecision(6)}, ${t.toPrecision(6)}] (a discontinuity was not located), so no exact value is given.`);
    checks.push(`piece [${s.toPrecision(6)}, ${t.toPrecision(6)}]: quadrature ${nq.value.toPrecision(12)} = F(t) - F(s) ${dF.toPrecision(12)}`);
  }

  const whole = numericSplit(f0, xs, a, b, digits);
  // 4b. divergence (or principal value)
  if (divergent) {
    if (opts.pv) {
      const pvRes = principalValue(F, xs, nodes, pieces);
      if (pvRes) {
        const value = pvRes;
        const approx = evalD(value);
        if (!Number.isFinite(approx)) return fallback("The principal value could not be evaluated.");
        log.add({ rule: "int.improper", title: "Cauchy principal value", why: "The integral diverges, but the symmetric limit (excluding (c - e, c + e) around each singular point, or [-R, R] for an infinite range) exists.", before: X.integral(f0, xs, a, b), after: value });
        return { status: "exact", value, approx, F, method: "int.improper", pv: true, conditions: ["Cauchy principal value (the ordinary improper integral diverges)"], checks };
      }
    }
    const { pt, side, Lr } = divergent;
    // the divergence proof rests on F' = f near that end: confirm it on a chain of intervals approaching it
    // (numerical quadrature is NOT trusted here: it can "converge" on a divergent integral, e.g. by symmetric
    // cancellation of x/(1 + x^2) over the whole line)
    if (!nearEndCheck(f0, F, xs, pieces[divergent.piece], side)) {
      throw intError("UNSUPPORTED", "The antiderivative could not be confirmed near the point where the integral appears to diverge, so Quelvra gives no answer.");
    }
    const where = isInf(pt.t) ? `as ${xs.name} -> ${pt.t === OO ? "+oo" : "-oo"}` : `as ${xs.name} -> ${T(pt.t)}${side === "+" ? "+" : "-"}`;
    const reason = `${where}, the antiderivative ${T(F)} ${Lr.k === "inf" ? "tends to " + limText(Lr, T) : "has no limit" + (Lr.reason ? " (" + Lr.reason + ")" : "")}, so the improper integral diverges.`;
    log.add({ rule: "int.improper", title: "Divergent improper integral", why: reason.charAt(0).toUpperCase() + reason.slice(1), before: X.integral(f0, xs, a, b), after: null });
    return { status: "diverges", reason: reason.charAt(0).toUpperCase() + reason.slice(1), F, checks };
  }

  // 4c. exact value
  let value = ZERO;
  for (const pc of pieces) value = X.add(value, pc.Lq.v, X.neg(pc.Lp.v));
  value = combineLogs(canon(value));
  const approx = evalD(value);
  if (!Number.isFinite(approx)) return fallback("The exact value could not be evaluated numerically.");
  if (whole && whole.converged && Number.isFinite(whole.value)) {
    const tolW = Math.max(10 * (Number.isFinite(whole.err) ? whole.err : 0), 1e-8 * Math.max(1, Math.abs(approx)));
    if (Math.abs(whole.value - approx) > tolW) return fallback(`The exact evaluation ${T(value)} disagreed with numerical quadrature (${whole.value}); the numerical value is reported instead.`, whole);
    checks.push(`whole interval: quadrature ${whole.value} agrees with ${approx}`);
  } else checks.push("whole-interval quadrature did not converge; value rests on the verified antiderivative, the one-sided limits and the piece checks");
  // steps
  const improper = !isFinite(av) || !isFinite(bv) || pieces.some((pc) => fSing(pc.p) || fSing(pc.q));
  for (const pc of pieces) {
    const sideTxt = (n, s) => (isInf(n.t) ? `lim(${xs.name} -> ${n.t === OO ? "oo" : "-oo"})` : (fSing(n) || interior.includes(n)) ? `lim(${xs.name} -> ${T(n.t)}${s})` : `F(${T(n.t)})`);
    log.add({ rule: improper || interior.length ? "int.improper" : "int.ftc", title: `Evaluate on [${T(pc.p.t)}, ${T(pc.q.t)}]`, why: `${sideTxt(pc.q, "-")} F = ${T(pc.Lq.v)} and ${sideTxt(pc.p, "+")} F = ${T(pc.Lp.v)}.`, before: X.integral(f0, xs, pc.p.t, pc.q.t), after: canon(X.sub(pc.Lq.v, pc.Lp.v)) });
  }
  if (pieces.length > 1) log.add({ rule: "int.ftc", title: "Add the pieces", why: "The integral over the whole interval is the sum over the pieces.", before: X.integral(f0, xs, a, b), after: value });
  return { status: "exact", value, approx, F, method: improper ? "int.improper" : "int.ftc", conditions: [...anti.conditions.filter((c) => !/tan\(/.test(c))], checks, antiMethod: anti.method };
}

// sum of q_i ln(n_i) with rational q_i and positive rational n_i -> (1/D) ln(prod n_i^(D q_i)), when shorter
function combineLogs(v) {
  if (v.k !== "add") return v;
  const logs = [], rest = [];
  for (const t of v.args) {
    let q = null, L = null;
    if (t.k === "fn" && t.name === "ln") { q = X.ONE; L = t; }
    else if (t.k === "mul" && t.args.length === 2 && X.isNum(t.args[0]) && t.args[1].k === "fn" && t.args[1].name === "ln") { q = t.args[0]; L = t.args[1]; }
    if (L && X.isNum(L.args[0]) && L.args[0].v.n > 0n) logs.push({ q: q.v, n: L.args[0] }); else rest.push(t);
  }
  if (logs.length < 2) return v;
  let D = 1n;
  const g = (a, b) => (b ? g(b, a % b) : a);
  for (const { q } of logs) D = (D * q.d) / g(D, q.d);
  if (D > 12n) return v;
  let prod = X.ONE;
  for (const { q, n } of logs) {
    const e = (q.n * D) / q.d;
    if (e > 40n || e < -40n) return v;
    prod = X.mul(prod, X.pow(n, X.num(e)));
  }
  const pv = canon(prod);
  if (!X.isNum(pv)) return v;
  const c = canon(X.add(...rest, X.mul(X.num(1n, D), X.fn("ln", pv))));
  return toText(c).length < toText(v).length ? c : v;
}

// F(t_{k+1}) - F(t_k) = integral of f over [t_k, t_{k+1}] for points t_k approaching the divergent end
function nearEndCheck(f, F, x, piece, side) {
  const fx = (t) => evalD(f, { [x.name]: t }), Fx = (t) => evalD(F, { [x.name]: t });
  const end = side === "+" ? piece.p : piece.q, other = side === "+" ? piece.q : piece.p;
  const ts = [];
  if (Number.isFinite(end.v)) {
    const span = Number.isFinite(other.v) ? Math.abs(other.v - end.v) : 1;
    const dir = side === "+" ? 1 : -1;
    for (const k of [1e-1, 1e-2, 1e-3, 1e-4, 1e-5]) ts.push(end.v + dir * span * k);
  } else {
    const sgn = end.v > 0 ? 1 : -1;
    const base = Number.isFinite(other.v) ? other.v : 0;
    for (const R of [10, 100, 1000, 10000]) ts.push(base + sgn * R);
  }
  let checked = 0;
  for (let i = 0; i + 1 < ts.length; i++) {
    const a = Math.min(ts[i], ts[i + 1]), b = Math.max(ts[i], ts[i + 1]);
    const q = quad(fx, a, b, 1e-10, 3000);
    const dF = Fx(b) - Fx(a);
    if (!q.ok || !Number.isFinite(dF)) continue;
    checked++;
    if (Math.abs(q.value - dF) > 1e-6 * Math.max(1, Math.abs(dF)) + 10 * q.err) return false;
  }
  return checked >= 2;
}

// F at a finite end of a piece: plain substitution where neither f nor F breaks (F is continuous there),
// a one-sided limit otherwise
// erf(0) = Si(0) = ... = 0 (the simplifier does not know the integrator's special functions)
const ODD_SPECIAL = new Set(["erf", "erfi", "Si", "Shi", "FresnelS", "FresnelC"]);
function oddSpecialZero(u) {
  if (!u.args || !u.args.length) return u;
  const a = u.args.map(oddSpecialZero);
  if (u.k === "fn" && ODD_SPECIAL.has(u.name) && a.length === 1 && canon(a[0]) === ZERO) return ZERO;
  return a.every((t, i) => t === u.args[i]) ? u : X.withArgs(u, a);
}

function endValue(F, x, node, side, breaks) {
  const isBreak = breaks.some((b) => Math.abs(b.v - node.v) < 1e-12 * Math.max(1, Math.abs(node.v)));
  if (!isBreak) {
    try {
      const v = canon(oddSpecialZero(X.subs(F, { [x.name]: node.t })));
      if (Number.isFinite(evalD(v)) && !X.contains(v, X.UNDEF)) return { k: "fin", v };
    } catch (e) { if (!e || !e.code) throw e; }
  }
  return lim(F, x, node.t, side);
}

// principal value: pair F(c-) - F(c+) at interior singular points as lim_{e->0+} [F(c - e) - F(c + e)],
// and F(b) - F(a) for a = -oo, b = oo as lim_{R->oo} [F(R) - F(-R)]
function principalValue(F, x, nodes, pieces) {
  const e = X.sym("__e");
  let value = ZERO;
  const first = pieces[0], last = pieces[pieces.length - 1];
  // endpoints
  if (isNegInf(first.p.t) && last.q.t === OO && (first.Lp.k !== "fin" || last.Lq.k !== "fin")) {
    const r = lim(X.sub(X.subs(F, { [x.name]: e }), X.subs(F, { [x.name]: X.neg(e) })), e, OO, "");
    if (r.k !== "fin") return null;
    value = X.add(value, r.v);
  } else {
    if (first.Lp.k !== "fin" || last.Lq.k !== "fin") return null;
    value = X.add(value, last.Lq.v, X.neg(first.Lp.v));
  }
  for (let i = 0; i + 1 < pieces.length; i++) {
    const c = pieces[i].q, L = pieces[i].Lq, R = pieces[i + 1].Lp;
    if (L.k === "fin" && R.k === "fin") { value = X.add(value, L.v, X.neg(R.v)); continue; }
    const r = lim(X.sub(X.subs(F, { [x.name]: X.sub(c.t, e) }), X.subs(F, { [x.name]: X.add(c.t, e) })), e, ZERO, "+");
    if (r.k !== "fin") return null;
    value = X.add(value, r.v);
  }
  return canon(value);
}

// parameters in f or symbolic limits: F(b) - F(a) only when F cannot break anywhere relevant
function symbolicDefinite(f0, x, a, b, opts, log) {
  let anti;
  try { anti = integrate(f0, x, { steps: new StepLog(), timeLimit: opts.timeLimit || 6000 }); } catch (e) {
    if (e && e.code) throw intError("UNSUPPORTED", "No verified antiderivative was found for this integral with symbolic parameters.");
    throw e;
  }
  const F = anti.F;
  const bf = breakPoints(f0, x, -Infinity, Infinity), bF = breakPoints(F, x, -Infinity, Infinity);
  const nodesAny = (u) => X.contains(u, OO);
  if (nodesAny(a) || nodesAny(b)) throw intError("UNSUPPORTED", "Improper integrals with symbolic parameters are not supported.");
  const hasBreak = (u) => {
    let found = false;
    const walk = (w) => {
      if (found || X.freeOf(w, x)) return;
      for (const s of w.args) walk(s);
      if (w.k === "pow" && !X.freeOf(w.args[0], x) && (!X.isNum(w.args[1]) || w.args[1].v.n < 0n || w.args[1].v.d !== 1n)) found = true;
      if (w.k === "fn" && !["sin", "cos", "exp", "atan", "sinh", "cosh", "tanh", "asinh", "abs", "erf", "erfi", "Si", "Shi", "FresnelS", "FresnelC", "acot"].includes(w.name)) found = true;
    };
    walk(u);
    return found;
  };
  void bf; void bF;
  if (hasBreak(f0) || hasBreak(F)) throw intError("UNSUPPORTED", "With symbolic parameters Quelvra cannot confirm that the antiderivative is continuous between the limits, so it does not apply the fundamental theorem of calculus.");
  const value = canon(X.sub(X.subs(F, { [x.name]: b }), X.subs(F, { [x.name]: a })));
  log.add({ rule: "int.ftc", title: "Fundamental theorem of calculus", why: `F(${x.name}) = ${T(F)} is continuous for every real ${x.name}, so the integral is F(${T(b)}) - F(${T(a)}).`, before: X.integral(f0, x, a, b), after: value });
  return { status: "exact", value, approx: NaN, F, method: "int.ftc", conditions: [], checks: ["antiderivative verified; F continuous on the real line"] };
}

export { breakPoints, NEG_OO };
