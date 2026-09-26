// Differential geometry of curves: curvature (of r(t) and of a graph y = f(x)), torsion, the
// Frenet frame T, N, B, and the arc-length parametrisation r(s).
//
// Solver: exact symbolic derivatives and the cross-product formulas
//   kappa = |r' x r''| / |r'|^3,  tau = (r' x r'') . r''' / |r' x r''|^2,
//   T = r'/|r'|,  N = ((r' x r'') x r') / (|r' x r''| |r'|),  B = (r' x r'') / |r' x r''|,
//   kappa for y = f(x): |f''| / (1 + f'^2)^(3/2).
// Verification (independent): finite differences (Richardson) of the ORIGINAL r(t) or f(x); N is
// checked as the normalised finite-difference derivative of T (not the cross-product formula);
// r(s) is checked by numerically inverting the quadrature arc-length function s(t).

import { solve as orchestrate } from "../orchestrate.js";
import { integrate } from "../calc/integrate.js";
import {
  X, toText, TCV, fail, safe, pass, bad, open, fmt, C, D, nice, tidyTrig, isZeroExact, isVec, vecArgs, sqrtTidy,
  evalR, forEval, envFn, probePoints, closeTo, quad1, numOf,
} from "./util.js";

const S = X.sym;
// ------------------------------------------------------------------ arguments
function curveArgs(node, name, { dims = [2, 3] } = {}) {
  const r0 = vecArgs(node.args[0]);
  if (!r0) return null;
  if (!dims.includes(r0.length)) throw fail(`${name} needs a curve r(t) with ${dims.join(" or ")} components`);
  const tv = node.args[1];
  if (!tv || tv.k !== "sym") throw fail(`give the parameter, for example ${name}([cos(t), sin(t), t], t)`);
  const t = tv.name;
  const r = r0.map((c) => C(c));
  const extra = r.flatMap((c) => [...X.freeSymbols(c)]).filter((v) => v !== t);
  if (extra.length) throw fail(`the curve may only depend on ${t} (found ${[...new Set(extra)].join(", ")})`);
  let t0 = null;
  if (node.args[2]) {
    t0 = C(node.args[2]);
    if (X.freeSymbols(t0).size || !Number.isFinite(numOf(t0))) throw fail("the parameter value must be a number");
  }
  if (node.args.length > 3) throw fail(`${name}(r(t), t[, t0])`);
  return { r, t, t0 };
}
const cross = (a, b) => [X.sub(X.mul(a[1], b[2]), X.mul(a[2], b[1])), X.sub(X.mul(a[2], b[0]), X.mul(a[0], b[2])), X.sub(X.mul(a[0], b[1]), X.mul(a[1], b[0]))];
const dot = (a, b) => X.add(...a.map((c, i) => X.mul(c, b[i])));
const norm = (a) => sqrtTidy(C(X.add(...a.map((c) => X.pow(c, X.TWO)))));
const pad3 = (v) => (v.length === 2 ? [...v, X.ZERO] : v);
// derivatives, substituted at t0 when given (exact numbers then)
function derivs(r, t, t0, k) {
  const out = [];
  let cur = r;
  for (let i = 0; i < k; i++) { cur = cur.map((c) => C(D(c, t))); out.push(cur); }
  return t0 ? out.map((v) => v.map((c) => C(X.subs(c, { [t]: t0 })))) : out;
}
const fin = (u) => tidyTrig(nice(u));
function nonzeroOrFail(u, what) {
  const z = isZeroExact(u);
  if (z === true) throw fail(`${what} is zero, so this quantity is undefined there`);
}

// ------------------------------------------------------------------ numeric derivatives (VERIFIER)
const hOf = (t, base) => base * Math.max(1, Math.abs(t));
const d1 = (g, t) => { const h = hOf(t, 1e-3); const c = (k) => (g(t + k) - g(t - k)) / (2 * k); return (4 * c(h / 2) - c(h)) / 3; };
const d2 = (g, t) => { const h = hOf(t, 1e-2); const c = (k) => (g(t + k) - 2 * g(t) + g(t - k)) / (k * k); return (4 * c(h / 2) - c(h)) / 3; };
const d3 = (g, t) => { const h = hOf(t, 2e-2); const c = (k) => (g(t + 2 * k) - 2 * g(t + k) + 2 * g(t - k) - g(t - 2 * k)) / (2 * k * k * k); return (4 * c(h / 2) - c(h)) / 3; };
const vnorm = (v) => Math.hypot(...v);
const vcross = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
const p3 = (v) => (v.length === 2 ? [...v, 0] : v);
function numFrame(r, t) {
  const fs = r.map((c) => { const g = envFn(c); return (s) => g({ [t]: s }); });
  const rp = (s) => p3(fs.map((g) => d1(g, s)));
  const rpp = (s) => p3(fs.map((g) => d2(g, s)));
  const rppp = (s) => p3(fs.map((g) => d3(g, s)));
  const T = (s) => { const v = rp(s); const n = vnorm(v); return v.map((c) => c / n); };
  const N = (s) => { const dT = [0, 1, 2].map((i) => d1((u) => T(u)[i], s)); const n = vnorm(dT); return dT.map((c) => c / n); };
  const kappa = (s) => vnorm(vcross(rp(s), rpp(s))) / Math.pow(vnorm(rp(s)), 3);
  const tau = (s) => { const c = vcross(rp(s), rpp(s)); const q = c.reduce((a, x) => a + x * x, 0); return (c[0] * rppp(s)[0] + c[1] * rppp(s)[1] + c[2] * rppp(s)[2]) / q; };
  return { fs, rp, T, N, kappa, tau };
}
// compare claimed(t) with numeric(t) at t0 or at probe points
function pointCheck(kind, t, t0, claimed, numeric, what, tol = 1e-6) {
  if (t0) {
    const tv = numOf(t0);
    const c = claimed(tv), n = numeric(tv);
    if (!Number.isFinite(c) || !Number.isFinite(n)) return open(kind, `the ${what} could not be evaluated numerically at ${t} = ${fmt(tv)}`);
    return closeTo(c, n, tol) ? pass(kind, `finite differences of the original curve give ${fmt(n)} at ${t} = ${fmt(tv)}`) : bad(kind, `finite differences give ${fmt(n)} at ${t} = ${fmt(tv)}, the answer gives ${fmt(c)}`);
  }
  let good = 0;
  for (const p of probePoints([t], 18, 11)) {
    if (good >= 6) break;
    const c = claimed(p[t]), n = numeric(p[t]);
    if (!Number.isFinite(c) || !Number.isFinite(n)) continue;
    if (!closeTo(c, n, tol)) return bad(kind, `at ${t} = ${fmt(p[t])} finite differences give ${fmt(n)}, the answer gives ${fmt(c)}`);
    good++;
  }
  return good >= 3 ? pass(kind, `the ${what} agrees with finite differences of the original curve at ${good} points`) : open(kind, "too few points where the curve could be evaluated");
}
const evalAt = (u, t) => { const g = forEval(u); return (s) => evalR(g, { [t]: s }); };

// ------------------------------------------------------------------ curvature
function graphCurvature(node, env) {
  const f = node.args[0];
  if (!f || ["eq", "rel", "matrix", "system"].includes(f.k)) throw fail("curvature(f(x), x[, x0]) or curvature([x(t), y(t)(, z(t))], t[, t0])");
  const xv = node.args[1] || X.sym("x");
  if (xv.k !== "sym") throw fail("give the variable, for example curvature(x^2, x)");
  const x = xv.name;
  const fx = C(f);
  const extra = [...X.freeSymbols(fx)].filter((v) => v !== x);
  if (extra.length) throw fail(`the function may only depend on ${x}`);
  let x0 = null;
  if (node.args[2]) { x0 = C(node.args[2]); if (X.freeSymbols(x0).size || !Number.isFinite(numOf(x0))) throw fail("the point must be a number"); }
  const at = (u) => (x0 ? C(X.subs(u, { [x]: x0 })) : u);
  const f1 = at(C(D(fx, x))), f2 = at(C(D(D(fx, x), x)));
  const kappa = fin(C(X.div(X.fn("abs", f2), X.pow(X.add(X.ONE, X.pow(f1, X.TWO)), X.num(3, 2)))));
  env.log.add({ rule: "curves.graph-curvature", title: "Curvature of a graph", why: `kappa = |f''| / (1 + f'^2)^(3/2) with f' = ${toText(f1)}, f'' = ${toText(f2)}${x0 ? ` at ${x} = ${toText(x0)}` : ""}.`, before: fx, after: kappa });
  const g = envFn(fx);
  const fn = (s) => g({ [x]: s });
  const numeric = (s) => Math.abs(d2(fn, s)) / Math.pow(1 + d1(fn, s) ** 2, 1.5);
  return { answers: answersFor("Curvature", kappa), verify: () => TCV([pointCheck("finite-differences", x, x0, evalAt(kappa, x), numeric, "curvature")]) };
}
function answersFor(label, tree) {
  const out = [{ kind: "exact", label, tree }];
  if (!X.freeSymbols(tree).size && !X.isNum(tree)) { const v = numOf(tree); if (Number.isFinite(v)) out.push({ kind: "approx", label, approx: { value: String(+v.toPrecision(15)), digits: 15, requested: 15, errorBound: (Math.abs(v) * 1e-14 + 1e-300).toExponential(1), method: "evaluation of the exact value", iterations: 0, converged: true } }); }
  return out;
}
function cmdCurvature(node, env) {
  const c = curveArgs(node, "curvature");
  if (!c) return graphCurvature(node, env);
  const { r, t, t0 } = c;
  const [r1, r2] = derivs(r, t, t0, 2);
  const cr = cross(pad3(r1), pad3(r2)).map((u) => C(u));
  const sp = norm(r1);
  nonzeroOrFail(sp, "the speed |r'|");
  const kappa = fin(C(X.div(norm(cr), X.pow(sp, X.num(3)))));
  env.log.add({ rule: "curves.curvature", title: "Curvature", why: `kappa = |r' x r''| / |r'|^3 with r' = (${r1.map(toText).join(", ")}), r'' = (${r2.map(toText).join(", ")}), |r'| = ${toText(sp)}.`, before: X.vector(...r), after: kappa });
  const F = numFrame(r, t);
  return { answers: answersFor("Curvature", kappa), verify: () => TCV([pointCheck("finite-differences", t, t0, evalAt(kappa, t), F.kappa, "curvature")]) };
}
function cmdTorsion(node, env) {
  const c = curveArgs(node, "torsion", { dims: [3] });
  if (!c) throw fail("torsion needs a space curve r(t) = [x(t), y(t), z(t)]");
  const { r, t, t0 } = c;
  const [r1, r2, r3] = derivs(r, t, t0, 3);
  const cr = cross(r1, r2).map((u) => C(u));
  const q = tidyTrig(C(X.add(...cr.map((u) => X.pow(u, X.TWO)))));
  nonzeroOrFail(q, "|r' x r''| (the curvature)");
  const tau = fin(C(X.div(dot(cr, r3), q)));
  env.log.add({ rule: "curves.torsion", title: "Torsion", why: `tau = (r' x r'') . r''' / |r' x r''|^2 with r' x r'' = (${cr.map(toText).join(", ")}), r''' = (${r3.map(toText).join(", ")}).`, before: X.vector(...r), after: tau });
  const F = numFrame(r, t);
  return { answers: answersFor("Torsion", tau), verify: () => TCV([pointCheck("finite-differences", t, t0, evalAt(tau, t), F.tau, "torsion", 2e-6)]) };
}
function frameVector(which) {
  return (node, env) => {
    const c = curveArgs(node, which === "B" ? "binormal" : which === "T" ? "unittangent" : "unitnormal", { dims: which === "B" ? [3] : [2, 3] });
    if (!c) throw fail(`${which === "B" ? "binormal" : which === "T" ? "unittangent" : "unitnormal"} needs a curve r(t) = [x(t), y(t)(, z(t))]`);
    const { r, t, t0 } = c;
    const dim = r.length;
    const [r1, r2] = derivs(r, t, t0, 2);
    const sp = norm(r1);
    nonzeroOrFail(sp, "the speed |r'|");
    let vec, why;
    if (which === "T") { vec = r1.map((u) => fin(C(X.div(u, sp)))); why = `T = r'/|r'| with |r'| = ${toText(sp)}.`; }
    else {
      const cr = cross(pad3(r1), pad3(r2)).map((u) => C(u));
      const cn = norm(cr);
      nonzeroOrFail(cn, "|r' x r''| (the curvature)");
      if (which === "B") { vec = cr.map((u) => fin(C(X.div(u, cn)))); why = `B = (r' x r'') / |r' x r''| with r' x r'' = (${cr.map(toText).join(", ")}).`; }
      else {
        const m = cross(cr, pad3(r1)).map((u) => C(u));
        vec = m.slice(0, dim).map((u) => fin(C(X.div(u, X.mul(cn, sp)))));
        why = `N = ((r' x r'') x r') / (|r' x r''| |r'|), the unit vector along T'.`;
      }
    }
    const tree = X.vector(...vec);
    const label = which === "T" ? "Unit tangent T" : which === "N" ? "Principal unit normal N" : "Binormal B";
    env.log.add({ rule: `curves.${which}`, title: label, why, before: X.vector(...r), after: tree });
    const F = numFrame(r, t);
    const num = which === "T" ? F.T : which === "N" ? F.N : (s) => vcross(F.T(s), F.N(s));
    return {
      answers: [{ kind: "exact", label, tree }],
      verify: () => TCV(vec.map((comp, i) => pointCheck(which === "N" ? "finite-difference-derivative-of-T" : "finite-differences", t, t0, evalAt(comp, t), (s) => num(s)[i], `component ${i + 1}`, 2e-6))),
    };
  };
}

// ------------------------------------------------------------------ arc-length parametrisation
function cmdArcparam(node, env) {
  const c = curveArgs(node, "arcparam");
  if (!c) throw fail("arcparam needs a curve r(t) = [x(t), y(t)(, z(t))]");
  const { r, t } = c;
  const t0 = c.t0 || X.ZERO;
  const t0v = numOf(t0);
  const [r1] = derivs(r, t, null, 1);
  const sp = norm(r1);
  const s = S("s");
  if (r.some((u) => X.hasSym(u, "s"))) throw fail("the curve already uses the letter s");
  let tOfS, sOfT;
  if (!X.hasSym(sp, t)) {
    const v = numOf(sp);
    if (!(v > 0)) throw fail("the speed must be positive");
    sOfT = C(X.mul(sp, X.sub(S(t), t0)));
    tOfS = C(X.add(t0, X.div(s, sp)));
  } else {
    // s(t) = integral of the speed from t0; invert when a single real branch exists
    let F;
    try { F = definite(sp, t, t0); } catch (e) { if (e && e.code === "TIMEOUT") throw e; throw fail("the arc length function s(t) has no closed form Quelvra can derive"); }
    sOfT = F;
    const sol = safe(() => orchestrate(X.eq(s, F), { variable: t, domain: "real" }));
    const cands = ((sol && sol.answers) || []).filter((a) => a.tree && a.kind === "exact").map((a) => (a.tree.k === "eq" ? a.tree.args[1] : a.tree)).filter((u) => !X.hasSym(u, t));
    const good = cands.filter((u) => { const v = safe(() => numOf(C(X.subs(u, { s: X.ZERO })))); return Number.isFinite(v) && Math.abs(v - t0v) < 1e-9; });
    if (good.length !== 1) throw fail("the arc length function s(t) cannot be inverted in closed form (one branch through the start point is needed)");
    tOfS = C(good[0]);
  }
  const R = r.map((u) => fin(C(X.subs(u, { [t]: tOfS }))));
  const tree = X.vector(...R);
  env.log.add({ rule: "curves.arcparam", title: "Arc-length parametrisation", why: `|r'(${t})| = ${toText(sp)}, so s = ${toText(sOfT)} measured from ${t} = ${toText(t0)}; solving for ${t} gives ${t} = ${toText(tOfS)}.`, before: X.vector(...r), after: tree });
  const Fr = numFrame(r, t);
  const speed = (u) => vnorm(Fr.rp(u));
  const arcTo = (u) => { if (u === t0v) return 0; const q = quad1(speed, Math.min(t0v, u), Math.max(t0v, u), { m: 16, panels: 8 }); return q.ok ? (u > t0v ? q.value : -q.value) : NaN; };
  const tFor = (sv) => {
    // numeric inverse of the quadrature arc length (Newton with the numeric speed as derivative)
    let u = t0v + sv / Math.max(1e-6, speed(t0v));
    for (let k = 0; k < 60; k++) { const e = arcTo(u) - sv; if (!Number.isFinite(e)) return NaN; const du = e / speed(u); u -= du; if (Math.abs(du) < 1e-13 * Math.max(1, Math.abs(u))) break; }
    return u;
  };
  const Rf = R.map((u) => evalAt(u, "s"));
  return {
    answers: [{ kind: "exact", label: "r(s)", tree }, { kind: "exact", label: "s(t)", tree: sOfT }],
    verify: () => {
      let good = 0;
      for (const sv of [0.37, 1.13, -0.61, 2.29, 0.05]) {
        const u = tFor(sv);
        if (!Number.isFinite(u)) continue;
        const want = Fr.fs.map((g) => g(u));
        const got = Rf.map((g) => g(sv));
        if (got.some((v) => !Number.isFinite(v)) || want.some((v) => !Number.isFinite(v))) continue;
        if (!got.every((v, i) => closeTo(v, want[i], 1e-7))) return TCV([bad("arc-length-inverse", `at s = ${fmt(sv)} the curve point at arc length s (quadrature) is (${want.map(fmt).join(", ")}), the answer gives (${got.map(fmt).join(", ")})`)]);
        good++;
      }
      return TCV([good >= 3 ? pass("arc-length-inverse", `r(s) matches the point of the original curve at arc length s (Gauss-Legendre quadrature of the finite-difference speed, inverted numerically) at ${good} values of s`) : open("arc-length-inverse", "too few values of s could be checked")]);
    },
  };
}
// s(t) = F(t) - F(t0) from an antiderivative; the verifier checks the resulting r(s) independently
function definite(f, t, t0) {
  const r = integrate(f, t);
  return C(X.sub(r.F, X.subs(r.F, { [t]: t0 })));
}

export const CURVES = {
  curvature: cmdCurvature, torsion: cmdTorsion,
  unittangent: frameVector("T"), unitnormal: frameVector("N"), binormal: frameVector("B"),
  arcparam: cmdArcparam,
};
// graph curvature is dispatched inside cmdCurvature (non-vector first argument)
export const graphCurvatureApplies = () => false;
