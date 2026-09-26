// Advanced continuous mathematics: shared helpers.
//
// Two separate toolkits live here and must stay separate:
//   * SOLVER side: symbolic helpers built on the canonicaliser, calc/diff.js, the integrators.
//   * VERIFIER side: plain double / complex numerics on the ORIGINAL input with the verifier's own
//     evaluator (verify.js evalC): finite differences, Gauss-Legendre quadrature, Newton searches.
// A verification never calls the symbolic routine that produced the answer.

import * as X from "../expr.js";
import * as Q from "../num.js";
import { simplify, makeCtx, expand, together, numerDenom } from "../simplify.js";
import { toText } from "../print.js";
import { evalC, truth } from "../verify.js";
import { diff as symDiff } from "../calc/diff.js";
import { approxRec, signConst, cmpConst } from "../solve/util.js";
import { trigsimp } from "../rules.js";
import { toContractVerification } from "../orchestrate.js";

export { X, Q, toText, evalC, truth, approxRec, signConst, cmpConst, expand, together, numerDenom };
export const TCV = toContractVerification;

// ------------------------------------------------------------------ errors and records
export function fail(message) { const e = new Error(message); e.code = "UNSUPPORTED"; return e; }
export const safe = (f) => { try { return f(); } catch (e) { if (e && e.code === "TIMEOUT") throw e; return null; } };
export const pass = (kind, detail, numeric = true) => ({ status: numeric ? "verified-numeric" : "verified-exact", checks: [{ kind, ok: true, detail }] });
export const bad = (kind, detail) => ({ status: "failed", checks: [{ kind, ok: false, detail }] });
export const open = (kind, detail) => ({ status: "inconclusive", checks: [{ kind, ok: null, detail }] });
export const fmt = (v) => (Number.isFinite(v) ? String(+v.toPrecision(10)) : String(v));
export const fmtC = (c) => (Math.abs(c.im) <= 1e-12 * Math.max(1, Math.abs(c.re)) ? fmt(c.re) : `${fmt(c.re)} ${c.im < 0 ? "-" : "+"} ${fmt(Math.abs(c.im))}i`);

// ------------------------------------------------------------------ SOLVER side: symbolic
const ctx = () => makeCtx({ budget: { ops: 600000 } });
export const C = (u) => simplify(u, ctx());
export const D = (u, v) => symDiff(u, typeof v === "string" ? X.sym(v) : v);
// the shortest of a few equivalent presentations
export function nice(u) {
  const c = C(u);
  const cands = [c];
  const e = safe(() => C(expand(c, ctx())));
  if (e) cands.push(e);
  const t = safe(() => C(together(c, ctx())));
  if (t) cands.push(t);
  const f = safe(() => { const [n, d] = numerDenom(together(c, ctx())); return C(X.div(C(expand(n, ctx())), C(expand(d, ctx())))); });
  if (f) cands.push(f);
  let best = c;
  for (const k of cands) if (k && k !== X.UNDEF && !X.contains(k, X.UNDEF) && toText(k).length < toText(best).length) best = k;
  return best;
}
const hasSinCos = (u) => (u.k === "fn" && (u.name === "sin" || u.name === "cos")) || (u.args || []).some(hasSinCos);
// trig-aware tidy (sin^2 + cos^2 -> 1 and friends); falls back to nice()
export function tidyTrig(u) {
  const a = nice(u);
  const b = safe(() => trigsimp(a, { maxMs: 400 }).result);
  const c = b ? nice(b) : null;
  let best = c && toText(c).length < toText(a).length ? c : a;
  if (hasSinCos(best)) {
    // Pythagorean rewrite: sin^2 -> 1 - cos^2 (or cos^2 -> 1 - sin^2), expand, keep if shorter
    for (const [from, to] of [["sin", "cos"], ["cos", "sin"]]) {
      const r = safe(() => {
        const m = X.mapTree(best, (w) => {
          if (w.k !== "pow" || !X.isInt(w.args[1]) || w.args[1].v.n < 2n) return w;
          const b0 = w.args[0];
          if (b0.k !== "fn" || b0.name !== from) return w;
          const k = w.args[1].v.n;
          const sq = X.sub(X.ONE, X.pow(X.fn(to, b0.args[0]), X.TWO));
          return X.mul(X.pow(sq, X.num(k / 2n)), k % 2n ? b0 : X.ONE);
        });
        return m === best ? null : nice(C(expand(C(m), ctx())));
      });
      if (r && r !== X.UNDEF && toText(r).length < toText(best).length) best = r;
    }
  }
  return best;
}
// exact zero test (canonical forms only; null = undecided)
export function isZeroExact(u) {
  const tries = [() => C(u), () => C(expand(C(u), ctx())), () => { const [n] = numerDenom(together(C(u), ctx())); return C(expand(n, ctx())); }, () => trigsimp(C(u), { maxMs: 300 }).result];
  for (const t of tries) { const r = safe(t); if (r === X.ZERO) return true; if (r && X.isNum(r)) return false; }
  return null;
}
export const isVec = (u) => !!u && (u.k === "vector" || u.k === "tuple");
export const vecArgs = (u) => (isVec(u) ? u.args : null);
export const isSymVec = (u) => isVec(u) && u.args.every((a) => a.k === "sym");
export const vecNode = (arr) => X.vector(...arr);
export const hasFree = (u, names) => [...X.freeSymbols(u)].some((s) => names.includes(s));
const PREF = ["x", "y", "z", "t", "s", "u", "v", "w", "r", "theta"];
export function sortVars(names) {
  return [...names].sort((a, b) => { const ia = PREF.indexOf(a), ib = PREF.indexOf(b); return (ia < 0 ? 99 : ia) - (ib < 0 ? 99 : ib) || a.localeCompare(b); });
}
// variables of an expression list: explicit vector of symbols, else x, y, z style defaults
export function varsOf(exprs, explicit, { min = 1 } = {}) {
  if (explicit) {
    if (!isSymVec(explicit)) throw fail("the variables must be a list of symbols, for example [x, y, z]");
    return explicit.args.map((a) => a.name);
  }
  const fs = new Set();
  for (const e of exprs) for (const s of X.freeSymbols(e)) fs.add(s);
  const vs = sortVars(fs);
  if (vs.length < min) throw fail(`need at least ${min} variable${min > 1 ? "s" : ""}`);
  return vs;
}
// field variables for an n-component field
export function fieldVars(F, explicit) {
  if (explicit) return varsOf([], explicit);
  const n = F.length;
  const std = n === 2 ? ["x", "y"] : n === 3 ? ["x", "y", "z"] : null;
  if (!std) throw fail("a vector field needs 2 or 3 components, or give the variables");
  const extra = sortVars(new Set(F.flatMap((c) => [...X.freeSymbols(c)]))).filter((s) => !std.includes(s));
  if (extra.length) throw fail(`the field has other symbols (${extra.join(", ")}); give the variables explicitly, for example [x, y, z]`);
  return std;
}
// a constant argument: exact tree plus double value
export function constArg(u, what) {
  if (!u) throw fail(`missing ${what}`);
  const s = C(u);
  if (X.freeSymbols(s).size) throw fail(`${what} must be a number, got ${toText(s)}`);
  const v = evalC(s, {}, "complex");
  if (!Number.isFinite(v.re) || Math.abs(v.im) > 1e-12 * Math.max(1, Math.abs(v.re))) throw fail(`${what} must be a real number, got ${toText(s)}`);
  return { tree: s, v: v.re };
}
export function complexConst(u, what) {
  if (!u) throw fail(`missing ${what}`);
  const s = C(u);
  if (X.freeSymbols(s).size) throw fail(`${what} must be a number, got ${toText(s)}`);
  const v = evalC(s, {}, "complex");
  if (!Number.isFinite(v.re) || !Number.isFinite(v.im)) throw fail(`${what} is not a finite number`);
  return { tree: s, v };
}
export function exprArg(u, what) {
  if (!u) throw fail(`missing ${what}`);
  if (u.k === "eq" && u.args[0].k === "sym" && X.freeOf(u.args[1], u.args[0])) return u.args[1]; // "u = expr"
  if (["eq", "rel", "system", "and", "or", "vector", "tuple", "matrix"].includes(u.k)) throw fail(`${what} must be an expression`);
  return u;
}
// exact answer plus a decimal for constants
export function valueAnswers(label, tree, digits = 20) {
  const out = [{ kind: "exact", label, tree }];
  if (!X.freeSymbols(tree).size && !(X.isNum(tree) && tree.v.d === 1n) && !isVec(tree) && tree.k !== "matrix") {
    const ap = safe(() => approxRec(tree, digits));
    if (ap && !X.contains(tree, X.I)) out.push({ kind: "approx", label, approx: ap });
  }
  return out;
}
export function approxRecord(v, err, method, extra = {}) {
  const sc = Math.max(1e-300, Math.abs(v));
  const e = Math.max(err || 0, 1e-15 * Math.max(1, sc));
  const dg = Math.max(1, Math.min(15, Math.floor(-Math.log10(e / Math.max(1, sc)))));
  return { value: String(+v.toPrecision(Math.max(dg, 1))), digits: dg, requested: dg, errorBound: e.toExponential(1), method, iterations: extra.iterations || 0, converged: extra.converged !== false };
}

// ------------------------------------------------------------------ VERIFIER side: numerics
const isBad = (c) => !c || !Number.isFinite(c.re) || !Number.isFinite(c.im);
// heaviside is not known to the verifier's evaluator: rewrite it as a piecewise (value at the jump irrelevant)
export function forEval(u) {
  return X.mapTree(u, (w) => (w.k === "fn" && w.name === "heaviside" && w.args.length === 1 ? X.piecewise(X.ONE, X.rel(">", w.args[0], X.ZERO), X.ZERO, X.TRUE) : w));
}
export function evalR(u, env) { const c = evalC(u, env, "real"); return isBad(c) || Math.abs(c.im) > 1e-9 * Math.max(1, Math.abs(c.re)) ? NaN : c.re; }
export function evalZ(u, env) { const c = evalC(u, env, "complex"); return isBad(c) ? null : c; }
// real function of named variables
export function fnR(u, names) { const g = forEval(u); return (...xs) => { const env = {}; names.forEach((n, i) => { env[n] = xs[i]; }); return evalR(g, env); }; }

// Deterministic probe points in a box (avoid special values).
export function probePoints(names, count, seed = 1, lo = -2.2, hi = 2.4) {
  let s = (seed * 2654435761) >>> 0;
  const rnd = () => { s = (s + 0x6d2b79f5) >>> 0; let t = s; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
  const out = [];
  for (let i = 0; i < count; i++) { const p = {}; for (const n of names) p[n] = lo + (hi - lo) * rnd() + 0.0137 * (i + 1); out.push(p); }
  return out;
}
// Mixed partial derivative by nested central differences with one Richardson step.
const STEP = [0, 1e-3, 6e-3, 2e-2, 4e-2, 6e-2];
export function fdPartial(f, env, seq) {
  if (!seq.length) return f(env);
  const v = seq[0], rest = seq.slice(1);
  const k = seq.length;
  const h0 = (STEP[k] || 0.08) * Math.max(1, Math.abs(env[v]));
  const cd = (h) => (fdPartial(f, { ...env, [v]: env[v] + h }, rest) - fdPartial(f, { ...env, [v]: env[v] - h }, rest)) / (2 * h);
  const a = cd(h0), b = cd(h0 / 2);
  return (4 * b - a) / 3;
}
export function envFn(u) { const g = forEval(u); return (env) => evalR(g, env); }
// compare a claimed tree with a numeric reference at a point
export function closeTo(claim, ref, tol = 1e-5) {
  return Number.isFinite(claim) && Number.isFinite(ref) && Math.abs(claim - ref) <= tol * Math.max(1, Math.abs(ref), Math.abs(claim));
}
// Check claimed(env) == numeric(env) at random points where both are defined.
export function probeCheck(kind, names, claimedFn, numericFn, { count = 6, tol = 1e-5, need = 3, seed = 7, what = "value" } = {}) {
  let good = 0;
  for (const p of probePoints(names, 3 * count, seed)) {
    if (good >= count) break;
    const c = claimedFn(p), n = numericFn(p);
    if (!Number.isFinite(c) || !Number.isFinite(n)) continue;
    if (!closeTo(c, n, tol)) return bad(kind, `at ${fmtEnv(p)} the ${what} is ${fmt(n)} numerically but the answer gives ${fmt(c)}`);
    good++;
  }
  if (good < need) return open(kind, "too few points where the expressions could be evaluated");
  return pass(kind, `agrees with an independent finite-difference / quadrature computation at ${good} random points`);
}
export const fmtEnv = (p) => Object.entries(p).map(([k, v]) => `${k} = ${fmt(v)}`).join(", ");

// Gauss-Legendre nodes / weights on [-1, 1] (Newton on P_n)
const GLC = new Map();
export function glNodes(n) {
  if (GLC.has(n)) return GLC.get(n);
  const xs = [], ws = [];
  for (let i = 1; i <= n; i++) {
    let x = Math.cos((Math.PI * (i - 0.25)) / (n + 0.5));
    for (let it = 0; it < 100; it++) {
      let p0 = 1, p1 = x;
      for (let k = 2; k <= n; k++) { const p2 = ((2 * k - 1) * x * p1 - (k - 1) * p0) / k; p0 = p1; p1 = p2; }
      const dp = (n * (x * p1 - p0)) / (x * x - 1);
      const dx = p1 / dp;
      x -= dx;
      if (Math.abs(dx) < 1e-16) break;
    }
    let p0 = 1, p1 = x;
    for (let k = 2; k <= n; k++) { const p2 = ((2 * k - 1) * x * p1 - (k - 1) * p0) / k; p0 = p1; p1 = p2; }
    const dp = (n * (x * p1 - p0)) / (x * x - 1);
    xs.push(x); ws.push(2 / ((1 - x * x) * dp * dp));
  }
  const r = { xs, ws };
  GLC.set(n, r);
  return r;
}
// composite Gauss-Legendre on [a, b] with `panels` panels of order m
export function glPanel(g, a, b, m = 12, panels = 8) {
  const { xs, ws } = glNodes(m);
  let s = 0;
  const h = (b - a) / panels;
  for (let p = 0; p < panels; p++) {
    const c = a + (p + 0.5) * h, r = h / 2;
    for (let i = 0; i < m; i++) { const v = g(c + r * xs[i]); if (!Number.isFinite(v)) return NaN; s += ws[i] * v * r; }
  }
  return s;
}
// 1D integral with an error estimate from two resolutions
export function quad1(g, a, b, { m = 12, panels = 8 } = {}) {
  const v1 = glPanel(g, a, b, m, panels), v2 = glPanel(g, a, b, m, panels * 2);
  if (!Number.isFinite(v1) || !Number.isFinite(v2)) return { ok: false };
  return { ok: true, value: v2, err: Math.abs(v2 - v1) };
}
// Nested integral: levels [{ lo(env), hi(env), name }] from OUTER to INNER; g(env) the integrand.
export function nestedQuad(g, levels, { m = 10, panels = 6 } = {}) {
  const rec = (i, env, pm) => {
    if (i === levels.length) return g(env);
    const L = levels[i];
    const a = L.lo(env), b = L.hi(env);
    if (!Number.isFinite(a) || !Number.isFinite(b)) return NaN;
    if (a === b) return 0;
    return glPanel((t) => rec(i + 1, { ...env, [L.name]: t }, pm), a, b, m, pm);
  };
  const v1 = rec(0, {}, panels), v2 = rec(0, {}, panels * 2);
  if (!Number.isFinite(v1) || !Number.isFinite(v2)) return { ok: false };
  return { ok: true, value: v2, err: Math.abs(v2 - v1) };
}
// compare an exact/approx value with a numeric reference
export function valueCheck(kind, want, ref, what) {
  if (!ref.ok) return open(kind, `the independent ${what} did not converge`);
  const tol = Math.max(1e-8 * Math.max(1, Math.abs(want)), 20 * ref.err);
  if (tol > 1e-4 * Math.max(1, Math.abs(want))) return open(kind, `the independent ${what} is not accurate enough to confirm the value`);
  return Math.abs(want - ref.value) <= tol ? pass(kind, `independent ${what} gives ${fmt(ref.value)}`) : bad(kind, `independent ${what} gives ${fmt(ref.value)}, not ${fmt(want)}`);
}
// double / complex value of a constant tree (verifier evaluator)
export const numOf = (t) => evalR(forEval(t), {});
export const cnumOf = (t) => evalZ(forEval(t), {});

// Tanh-sinh on [0, oo) by t = u/(1 - u) mapping on [0, 1): for Laplace-type integrals.
export function quadHalfLine(g) {
  const h1 = (u) => { if (u >= 1) return 0; const t = u / (1 - u); const v = g(t); return v / ((1 - u) * (1 - u)); };
  const lev = (h) => {
    let s = 0;
    for (let k = -Math.ceil(3.2 / h); k <= Math.ceil(3.2 / h); k++) {
      const tt = k * h, uu = (Math.PI / 2) * Math.sinh(tt), ch = Math.cosh(uu);
      const w = ((Math.PI / 2) * Math.cosh(tt)) / (ch * ch);
      const y = Math.tanh(uu);
      const u = (1 + y) / 2;
      if (u <= 0 || u >= 1) continue;
      const v = h1(u);
      if (!Number.isFinite(v)) { if (w < 1e-12) continue; return NaN; }
      s += w * v * 0.5;
    }
    return s * h;
  };
  let prev = lev(0.5);
  for (let h = 0.25; h >= 1 / 128; h /= 2) {
    const cur = lev(h);
    if (!Number.isFinite(cur)) return { ok: false };
    if (Math.abs(cur - prev) <= 1e-11 * Math.max(1, Math.abs(cur))) return { ok: true, value: cur, err: Math.max(Math.abs(cur - prev), 1e-15 * Math.abs(cur)) };
    prev = cur;
  }
  return { ok: false };
}
// tanh-sinh on (-oo, oo) by t = u/(1 - u^2)
export function quadRealLine(g) {
  const lev = (h) => {
    let s = 0;
    for (let k = -Math.ceil(3.2 / h); k <= Math.ceil(3.2 / h); k++) {
      const tt = k * h, uu = (Math.PI / 2) * Math.sinh(tt), ch = Math.cosh(uu);
      const w = ((Math.PI / 2) * Math.cosh(tt)) / (ch * ch);
      const u = Math.tanh(uu);
      if (Math.abs(u) >= 1) continue;
      const d = 1 - u * u;
      const x = u / d, jac = (1 + u * u) / (d * d);
      const v = g(x) * jac;
      if (!Number.isFinite(v)) { if (w < 1e-12) continue; return NaN; }
      s += w * v;
    }
    return s * h;
  };
  let prev = lev(0.5);
  for (let h = 0.25; h >= 1 / 128; h /= 2) {
    const cur = lev(h);
    if (!Number.isFinite(cur)) return { ok: false };
    if (Math.abs(cur - prev) <= 1e-11 * Math.max(1, Math.abs(cur))) return { ok: true, value: cur, err: Math.max(Math.abs(cur - prev), 1e-15 * Math.abs(cur)) };
    prev = cur;
  }
  return { ok: false };
}
// solve a small dense linear system (partial pivoting); null when singular
export function linSolve(A, b) {
  const n = b.length;
  const M = A.map((r, i) => [...r, b[i]]);
  for (let c = 0; c < n; c++) {
    let p = c;
    for (let r = c + 1; r < n; r++) if (Math.abs(M[r][c]) > Math.abs(M[p][c])) p = r;
    if (Math.abs(M[p][c]) < 1e-14) return null;
    [M[c], M[p]] = [M[p], M[c]];
    for (let r = c + 1; r < n; r++) { const f = M[r][c] / M[c][c]; for (let k = c; k <= n; k++) M[r][k] -= f * M[c][k]; }
  }
  const x = new Array(n).fill(0);
  for (let r = n - 1; r >= 0; r--) { let s = M[r][n]; for (let k = r + 1; k < n; k++) s -= M[r][k] * x[k]; x[r] = s / M[r][r]; }
  return x;
}
// Newton's method for a system F: R^n -> R^n with a finite-difference Jacobian (verifier side)
export function newtonSystem(F, x0, { iters = 60, tol = 1e-12 } = {}) {
  let x = x0.slice();
  for (let it = 0; it < iters; it++) {
    const f = F(x);
    if (!f.every(Number.isFinite)) return null;
    const nrm = Math.hypot(...f);
    if (nrm < tol) return x;
    const n = x.length, J = [];
    for (let i = 0; i < n; i++) J.push(new Array(n).fill(0));
    for (let j = 0; j < n; j++) {
      const h = 1e-7 * Math.max(1, Math.abs(x[j]));
      const xp = x.slice(); xp[j] += h;
      const xm = x.slice(); xm[j] -= h;
      const fp = F(xp), fm = F(xm);
      for (let i = 0; i < n; i++) J[i][j] = (fp[i] - fm[i]) / (2 * h);
    }
    const dx = linSolve(J, f.map((v) => -v));
    if (!dx) return null;
    let lam = 1, moved = false;
    for (let k = 0; k < 30; k++) {
      const xn = x.map((v, i) => v + lam * dx[i]);
      const fn = F(xn);
      if (fn.every(Number.isFinite) && Math.hypot(...fn) < nrm) { x = xn; moved = true; break; }
      lam /= 2;
    }
    if (!moved) return Math.hypot(...f) < 1e-9 ? x : null;
    if (Math.hypot(...dx) * lam < 1e-15 * Math.max(1, Math.hypot(...x))) return Math.hypot(...F(x)) < 1e-8 ? x : null;
  }
  return Math.hypot(...F(x)) < 1e-9 ? x : null;
}

// SOLVER side: remove abs(w) / sqrt(w^2) when w keeps one sign at all sample points of the
// integration region (points: env objects). A wrong choice cannot survive: every integral is
// checked afterwards by independent quadrature of the ORIGINAL integrand.
export function dropAbs(u, points) {
  const signOn = (w) => {
    const g = forEval(w);
    let pos = 0, neg = 0;
    for (const p of points) { const v = evalR(g, p); if (!Number.isFinite(v)) return 0; if (v > 1e-12) pos++; else if (v < -1e-12) neg++; }
    return pos && !neg ? 1 : neg && !pos ? -1 : 0;
  };
  const out = X.mapTree(u, (w) => {
    let arg = null;
    if (w.k === "fn" && w.name === "abs" && w.args.length === 1) arg = w.args[0];
    else if (w.k === "pow" && w.args[1] === X.HALF && w.args[0].k === "pow" && X.isInt(w.args[0].args[1]) && w.args[0].args[1].v.n === 2n) arg = w.args[0].args[0];
    if (!arg) return w;
    const s = signOn(arg);
    return s === 1 ? arg : s === -1 ? X.neg(arg) : w;
  });
  return out === u ? u : C(out);
}
// sqrt(S) with the common factors of S's terms pulled out: sqrt(sin(u)^4 + sin(u)^2 cos(u)^2)
// -> abs(sin(u)) sqrt(sin(u)^2 + cos(u)^2) -> abs(sin(u)). Every result is checked numerically.
export function sqrtTidy(S0) {
  const S = tidyTrig(S0);
  const plain = tidyTrig(X.sqrt(S));
  if (S.k !== "add") return plain;
  const fac = (t) => (t.k === "mul" ? t.args : [t]).map((f) => (f.k === "pow" && X.isInt(f.args[1]) && f.args[1].v.n > 0n ? [f.args[0], Number(f.args[1].v.n)] : [f, 1]));
  const lists = S.args.map(fac);
  const common = [];
  for (const [b, e] of lists[0]) {
    if (X.isNum(b)) continue;
    let m = e;
    for (const L of lists.slice(1)) { const hit = L.find(([b2]) => b2 === b); if (!hit) { m = 0; break; } m = Math.min(m, hit[1]); }
    if (m >= 2) common.push([b, m - (m % 2)]);
  }
  if (!common.length) return plain;
  const cf = X.mul(...common.map(([b, e]) => X.pow(b, X.num(e))));
  const R = tidyTrig(X.div(S, cf));
  const out = safe(() => C(X.mul(...common.map(([b, e]) => X.pow(X.fn("abs", b), X.num(e / 2))), X.sqrt(R))));
  if (!out) return plain;
  const t = tidyTrig(out);
  return t === X.UNDEF || X.contains(t, X.UNDEF) ? plain : t;
}
// sample points of an iterated region; levels INNER first [{ v, lo, hi }] (inner limits may use outer variables)
export function regionPoints(levels, n = 9) {
  const pts = [];
  const lin = (a, b) => Array.from({ length: n }, (_, i) => a + ((b - a) * (i + 0.5)) / n);
  const rec = (i, env) => {
    if (i < 0) { pts.push(env); return; }
    const L = levels[i];
    const a = evalR(forEval(L.lo), env), b = evalR(forEval(L.hi), env);
    if (!Number.isFinite(a) || !Number.isFinite(b)) return;
    for (const t of lin(a, b)) rec(i - 1, { ...env, [L.v]: t });
  };
  rec(levels.length - 1, {});
  return pts;
}
