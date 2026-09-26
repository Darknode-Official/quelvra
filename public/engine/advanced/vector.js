// Vector calculus: divergence, curl, line integrals (scalar ds and vector dr), conservative fields
// and potentials, surface integrals and flux through parametrised surfaces, arc length of r(t).
//
// Verification: finite differences of the ORIGINAL field; for integrals, Gauss-Legendre quadrature
// of the original field along / over the original parametrisation with finite-difference
// tangent vectors (the symbolic r'(t), |r'(t)| and r_u x r_v used by the solver are not reused).
// A potential is certified by grad(phi) = F at random points; "not conservative" by a point where
// the finite-difference curl is clearly nonzero.

import { integrate } from "../calc/integrate.js";
import { definiteIntegral } from "../calc/int-definite.js";
import { iterate } from "./multint.js";
import {
  X, toText, TCV, fail, safe, pass, bad, open, fmt, C, D, nice, tidyTrig, isZeroExact, isVec, vecArgs, fieldVars, sortVars,
  valueAnswers, sqrtTidy, dropAbs, regionPoints, evalR, forEval, envFn, fdPartial, probePoints, probeCheck, fmtEnv, glPanel, nestedQuad, valueCheck, numOf,
} from "./util.js";

const fieldOf = (u, name) => {
  const F = vecArgs(u);
  if (!F || F.length < 2 || F.length > 3) throw fail(`${name} needs a vector field with 2 or 3 components, for example ${name}([x*y, y*z, z*x])`);
  return F.map((c) => C(c));
};

function cmdDiv(node, env) {
  const F = fieldOf(node.args[0], "div");
  const vars = fieldVars(F, node.args[1]);
  if (vars.length !== F.length) throw fail("the number of variables must match the number of components");
  const d = nice(X.add(...F.map((c, i) => D(c, vars[i]))));
  env.log.add({ rule: "vector.div", title: "Divergence", why: `div F = ${vars.map((v, i) => `d(F${i + 1})/d${v}`).join(" + ")}.`, before: X.vector(...F), after: d });
  const fe = F.map(envFn);
  return { answers: [{ kind: "exact", label: "div F", tree: d }], verify: () => TCV([probeCheck("finite-differences", vars, (p) => evalR(forEval(d), p), (p) => vars.reduce((s, v, i) => s + fdPartial(fe[i], p, [v]), 0), { tol: 1e-6, what: "divergence" })]) };
}
function curlParts(F, vars) {
  if (F.length === 2) return [nice(X.sub(D(F[1], vars[0]), D(F[0], vars[1])))];
  const [P, Q, R] = F, [x, y, z] = vars;
  return [nice(X.sub(D(R, y), D(Q, z))), nice(X.sub(D(P, z), D(R, x))), nice(X.sub(D(Q, x), D(P, y)))];
}
function numCurl(fe, vars, p) {
  const d = (i, j) => fdPartial(fe[i], p, [vars[j]]);
  if (fe.length === 2) return [d(1, 0) - d(0, 1)];
  return [d(2, 1) - d(1, 2), d(0, 2) - d(2, 0), d(1, 0) - d(0, 1)];
}
function cmdCurl(node, env) {
  const F = fieldOf(node.args[0], "curl");
  const vars = fieldVars(F, node.args[1]);
  const c = curlParts(F, vars);
  const tree = c.length === 1 ? c[0] : X.vector(...c);
  env.log.add({ rule: "vector.curl", title: F.length === 2 ? "Scalar curl" : "Curl", why: F.length === 2 ? "curl F = dQ/dx - dP/dy for F = (P, Q)." : "curl F = (R_y - Q_z, P_z - R_x, Q_x - P_y) for F = (P, Q, R).", before: X.vector(...F), after: tree });
  const fe = F.map(envFn);
  return { answers: [{ kind: "exact", label: "curl F", tree }], verify: () => TCV(c.map((ci, k) => probeCheck("finite-differences", vars, (p) => evalR(forEval(ci), p), (p) => numCurl(fe, vars, p)[k], { tol: 1e-6, what: `curl component ${k + 1}` }))) };
}

// ------------------------------------------------------------------ curves r(t)
function curveOf(node, name) {
  const r = vecArgs(node.args[1]);
  if (!r || r.length < 2 || r.length > 3) throw fail(`${name}: the curve must be a vector r(t) with 2 or 3 components`);
  const t = node.args[2];
  if (!t || t.k !== "sym") throw fail(`${name}: give the parameter, for example ${name}(F, [cos(t), sin(t)], t, 0, pi)`);
  if (!node.args[3] || !node.args[4] || node.args.length !== 5) throw fail(`${name}(F, r(t), t, a, b)`);
  const a = C(node.args[3]), b = C(node.args[4]);
  if (X.freeSymbols(a).size || X.freeSymbols(b).size) throw fail("the parameter limits must be numbers");
  const extra = r.flatMap((c) => [...X.freeSymbols(c)]).filter((s) => s !== t.name);
  if (extra.length) throw fail(`the curve may only depend on ${t.name}`);
  return { r: r.map((c) => C(c)), t: t.name, a, b };
}
// numeric r'(t) by central differences with Richardson
const numDeriv = (g, t) => { const h = 1e-3 * Math.max(1, Math.abs(t)); const cd = (k) => (g(t + k) - g(t - k)) / (2 * k); return (4 * cd(h / 2) - cd(h)) / 3; };
function lineQuad(integrandAt, a, b) {
  const v1 = glPanel(integrandAt, a, b, 16, 8), v2 = glPanel(integrandAt, a, b, 16, 16);
  if (!Number.isFinite(v1) || !Number.isFinite(v2)) return { ok: false };
  return { ok: true, value: v2, err: Math.abs(v2 - v1) };
}
const exactDefinite = (f, t, a, b, what) => {
  f = dropAbs(f, regionPoints([{ v: t, lo: a, hi: b }], 25));
  let r;
  try { r = definiteIntegral(f, t, a, b, {}); } catch (e) { if (e && e.code === "TIMEOUT") throw e; throw fail(`the ${what} could not be evaluated exactly`); }
  if (!r || r.status !== "exact") throw fail(`the ${what} has no closed form Quelvra can derive`);
  return nice(r.value);
};
function speedOf(r, t) {
  return sqrtTidy(X.add(...r.map((c) => X.pow(D(c, t), X.TWO))));
}
function cmdLineint(node, env) {
  const G = node.args[0];
  if (!G) throw fail("lineint(F, r(t), t, a, b)");
  const { r, t, a, b } = curveOf(node, "lineint");
  const cart = r.length === 2 ? ["x", "y"] : ["x", "y", "z"];
  const sub = Object.fromEntries(cart.map((v, i) => [v, r[i]]));
  let integrand, what;
  if (isVec(G)) {
    const F = G.args.map((c) => C(c));
    if (F.length !== r.length) throw fail("the field and the curve must have the same dimension");
    integrand = tidyTrig(X.add(...F.map((c, i) => X.mul(X.subs(c, sub), D(r[i], t)))));
    what = "vector";
    env.log.add({ rule: "vector.lineint", title: "Line integral of a vector field", why: `Integrate F(r(${t})) . r'(${t}) d${t} with r'(${t}) = (${r.map((c) => toText(nice(D(c, t)))).join(", ")}).`, before: X.vector(...F), after: integrand });
  } else {
    if (["eq", "matrix"].includes(G.k)) throw fail("lineint needs a scalar function or a vector field");
    const speed = speedOf(r, t);
    integrand = tidyTrig(X.mul(X.subs(C(G), sub), speed));
    what = "scalar";
    env.log.add({ rule: "vector.lineint.ds", title: "Line integral with respect to arc length", why: `ds = |r'(${t})| d${t} = ${toText(speed)} d${t}.`, before: G, after: integrand });
  }
  const extra = [...X.freeSymbols(integrand)].filter((s) => s !== t);
  if (extra.length) throw fail(`the integrand has symbols other than the field variables (${extra.join(", ")})`);
  const value = exactDefinite(integrand, t, a, b, "line integral");
  // verifier
  const rf = r.map(envFn);
  const av = numOf(a), bv = numOf(b);
  const pt = (s) => Object.fromEntries(cart.map((v, i) => [v, rf[i]({ [t]: s })]));
  const dr = (s) => rf.map((g) => numDeriv((u) => g({ [t]: u }), s));
  let fn;
  if (what === "vector") { const fe = G.args.map(envFn); fn = (s) => { const p = pt(s), d = dr(s); return fe.reduce((acc, g, i) => acc + g(p) * d[i], 0); }; }
  else { const ge = envFn(G); fn = (s) => ge(pt(s)) * Math.hypot(...dr(s)); }
  return { answers: valueAnswers("Line integral", value), verify: () => TCV([valueCheck("quadrature", numOf(value), lineQuad(fn, av, bv), "Gauss-Legendre quadrature along the curve (finite-difference tangent)")]) };
}
export function paramArclength(node, env) {
  const { r, t, a, b } = curveOf({ args: [null, ...node.args] }, "arclength");
  const speed = speedOf(r, t);
  env.log.add({ rule: "vector.arclength", title: "Arc length of a parametrised curve", why: `L = integral of |r'(${t})| d${t} with |r'(${t})| = ${toText(speed)}.`, before: X.vector(...r), after: speed });
  const value = exactDefinite(speed, t, a, b, "arc length");
  const rf = r.map(envFn);
  const fn = (s) => Math.hypot(...rf.map((g) => numDeriv((u) => g({ [t]: u }), s)));
  return { answers: valueAnswers("Arc length", value), verify: () => TCV([valueCheck("quadrature", numOf(value), lineQuad(fn, numOf(a), numOf(b)), "Gauss-Legendre quadrature of the finite-difference speed")]) };
}

// ------------------------------------------------------------------ conservative fields
function isEntire(u) {
  let ok = true;
  const walk = (w) => {
    if (!ok) return;
    if (w.k === "pow" && !(X.isInt(w.args[1]) && w.args[1].v.n >= 0n) && w.args[0] !== X.E) ok = false;
    if (w.k === "fn" && !["sin", "cos", "sinh", "cosh", "exp"].includes(w.name)) ok = false;
    for (const a of w.args) walk(a);
  };
  walk(u);
  return ok;
}
function buildPotential(F, vars, env) {
  let phi = X.ZERO;
  for (let i = 0; i < vars.length; i++) {
    const g = C(X.sub(F[i], D(phi, vars[i])));
    for (let j = 0; j < i; j++) if (isZeroExact(D(g, vars[j])) === false) return null;
    const gz = isZeroExact(g) === true ? X.ZERO : g;
    if (gz === X.ZERO) continue;
    let res;
    try { res = integrate(gz, vars[i]); } catch (e) { if (e && e.code === "TIMEOUT") throw e; throw fail(`could not integrate ${toText(gz)} with respect to ${vars[i]}`); }
    env.log.add({ rule: "vector.potential", title: `Integrate with respect to ${vars[i]}`, why: i === 0 ? `phi = integral of F1 d${vars[0]} + (function of the other variables).` : `The part of F${i + 1} not yet accounted for depends only on ${vars.slice(i).join(", ")}; integrate it in ${vars[i]}.`, before: gz, after: res.F });
    phi = C(X.add(phi, res.F));
  }
  return tidyTrig(phi);
}
function potentialCheck(phi, F, vars) {
  const pe = envFn(phi), fe = F.map(envFn);
  return vars.map((v, i) => probeCheck("gradient-certificate", vars, (p) => fdPartial(pe, p, [v]), (p) => fe[i](p), { tol: 1e-6, what: `d phi/d${v} against F${i + 1}` }));
}
function nonzeroCurlWitness(F, vars) {
  const c = curlParts(F, vars);
  const cand = [[1, 2, 3], [2, -1, 1], [1, 1, 1], [3, 1, -2], [-1, 2, 5]].map((xs) => xs.map((v) => X.num(v)));
  for (const pt of cand) {
    const m = Object.fromEntries(vars.map((v, i) => [v, pt[i]]));
    for (let k = 0; k < c.length; k++) {
      const val = safe(() => C(X.subs(c[k], m)));
      if (val && !X.freeSymbols(val).size && val !== X.UNDEF && isZeroExact(val) === false) return { pt: m, k, val };
    }
  }
  return null;
}
function conservativeCore(node, env, name) {
  const F = fieldOf(node.args[0], name);
  const vars = fieldVars(F, node.args[1]);
  const c = curlParts(F, vars);
  const zero = c.map((ci) => isZeroExact(ci));
  if (zero.some((z) => z === false)) {
    const w = nonzeroCurlWitness(F, vars);
    if (!w) throw fail("could not decide whether the curl vanishes");
    return { conservative: false, F, vars, c, w };
  }
  if (zero.some((z) => z !== true)) throw fail("could not decide whether the curl vanishes");
  const phi = buildPotential(F, vars, env);
  if (!phi) throw fail("could not construct a potential");
  return { conservative: true, F, vars, phi, entire: F.every(isEntire) };
}
function falseVerify(r) {
  return () => {
    const fe = r.F.map(envFn);
    const p = Object.fromEntries(Object.entries(r.w.pt).map(([k, v]) => [k, numOf(v)]));
    const nc = numCurl(fe, r.vars, p)[r.w.k];
    const want = numOf(r.w.val);
    return TCV([Number.isFinite(nc) && Math.abs(nc) > 1e-4 && Math.abs(nc - want) < 1e-5 * Math.max(1, Math.abs(want)) ? pass("curl-witness", `the finite-difference curl at ${fmtEnv(p)} is ${fmt(nc)}, not 0, so F is not a gradient`) : bad("curl-witness", "the curl witness could not be confirmed numerically")]);
  };
}
function cmdConservative(node, env) {
  const r = conservativeCore(node, env, "conservative");
  if (!r.conservative) {
    env.log.add({ rule: "vector.conservative.no", title: "The curl does not vanish", why: `At ${Object.entries(r.w.pt).map(([k, v]) => `${k} = ${toText(v)}`).join(", ")} the curl ${r.F.length === 2 ? "Q_x - P_y" : `component ${r.w.k + 1}`} equals ${toText(r.w.val)}, and a gradient field has zero curl.`, before: X.vector(...r.F), after: r.c.length === 1 ? r.c[0] : X.vector(...r.c) });
    return { answers: [{ kind: "exact", label: "Conservative", tree: X.FALSE }], verify: falseVerify(r) };
  }
  if (!r.entire) {
    return {
      answers: [{ kind: "exact", label: "potential", tree: r.phi, note: "grad phi = F wherever F and phi are defined; F is conservative on each region where phi is defined and single-valued" }],
      conditions: [], verify: () => TCV(potentialCheck(r.phi, r.F, r.vars)),
    };
  }
  env.log.add({ rule: "vector.conservative.yes", title: "Conservative", why: "F is defined on all of space and equals the gradient of phi.", before: X.vector(...r.F), after: r.phi });
  return { answers: [{ kind: "exact", label: "Conservative", tree: X.TRUE }, { kind: "exact", label: "potential", tree: r.phi }], verify: () => TCV(potentialCheck(r.phi, r.F, r.vars)) };
}
function cmdPotential(node, env) {
  const r = conservativeCore(node, env, "potential");
  if (!r.conservative) throw fail(`the field is not conservative: its curl is ${toText(r.c.length === 1 ? r.c[0] : X.vector(...r.c))}, so it has no potential function`);
  return { answers: [{ kind: "exact", label: "potential", tree: r.phi }], verify: () => TCV(potentialCheck(r.phi, r.F, r.vars)) };
}

// ------------------------------------------------------------------ surfaces r(u, v)
function surfaceOf(node, name) {
  const r = vecArgs(node.args[1]);
  if (!r || r.length !== 3) throw fail(`${name}: the surface must be a vector r(u, v) with 3 components`);
  if (node.args.length !== 8) throw fail(`${name}(F, r(u, v), u, a, b, v, c, d)`);
  const [, , u, a, b, v, c, d] = node.args;
  if (u.k !== "sym" || v.k !== "sym") throw fail(`${name}: the parameters must be variables`);
  const lim = [a, b, c, d].map((q) => C(q));
  if (X.freeSymbols(lim[2]).size || X.freeSymbols(lim[3]).size) throw fail("the outer limits must be numbers");
  if ([...X.freeSymbols(lim[0]), ...X.freeSymbols(lim[1])].some((s) => s !== v.name)) throw fail(`the limits of ${u.name} may only depend on ${v.name}`);
  const extra = r.flatMap((q) => [...X.freeSymbols(q)]).filter((s) => s !== u.name && s !== v.name);
  if (extra.length) throw fail(`the surface may only depend on ${u.name} and ${v.name}`);
  return { r: r.map((q) => C(q)), u: u.name, v: v.name, lim };
}
const crossT = (p, q) => [X.sub(X.mul(p[1], q[2]), X.mul(p[2], q[1])), X.sub(X.mul(p[2], q[0]), X.mul(p[0], q[2])), X.sub(X.mul(p[0], q[1]), X.mul(p[1], q[0]))];
const crossN = (p, q) => [p[1] * q[2] - p[2] * q[1], p[2] * q[0] - p[0] * q[2], p[0] * q[1] - p[1] * q[0]];
function surfaceIntegral(node, env, kind) {
  const G = node.args[0];
  if (!G) throw fail(`${kind}(F, r(u, v), u, a, b, v, c, d)`);
  const { r, u, v, lim } = surfaceOf(node, kind);
  const ru = r.map((q) => D(q, u)), rv = r.map((q) => D(q, v));
  const n = crossT(ru, rv).map(tidyTrig);
  const sub = { x: r[0], y: r[1], z: r[2] };
  let integrand;
  if (kind === "flux") {
    const F = vecArgs(G);
    if (!F || F.length !== 3) throw fail("flux needs a 3-component vector field");
    integrand = tidyTrig(X.add(...F.map((c, i) => X.mul(X.subs(C(c), sub), n[i]))));
    env.log.add({ rule: "vector.flux", title: "Flux integral", why: `Integrate F(r(${u}, ${v})) . (r_${u} x r_${v}) with r_${u} x r_${v} = (${n.map(toText).join(", ")}) (orientation of r_${u} x r_${v}).`, before: X.vector(...F), after: integrand });
  } else {
    if (["eq", "vector", "tuple", "matrix"].includes(G.k)) throw fail("surfint needs a scalar function");
    const dS = sqrtTidy(X.add(...n.map((c) => X.pow(c, X.TWO))));
    integrand = tidyTrig(X.mul(X.subs(C(G), sub), dS));
    env.log.add({ rule: "vector.surfint", title: "Surface integral", why: `dS = |r_${u} x r_${v}| d${u} d${v} = ${toText(dS)} d${u} d${v}.`, before: G, after: integrand });
  }
  const extra = [...X.freeSymbols(integrand)].filter((s) => s !== u && s !== v);
  if (extra.length) throw fail(`the integrand has symbols other than x, y, z (${extra.join(", ")})`);
  const value = nice(iterate(integrand, [{ v: u, lo: lim[0], hi: lim[1] }, { v, lo: lim[2], hi: lim[3] }], env, kind === "flux" ? "flux" : "surface integral"));
  // verifier: finite-difference r_u, r_v of the original parametrisation, original field
  const rf = r.map(envFn);
  const P = (p) => ({ x: rf[0](p), y: rf[1](p), z: rf[2](p) });
  const partial = (p, w) => rf.map((g) => numDeriv((s) => g({ ...p, [w]: s }), p[w]));
  let fnum;
  if (kind === "flux") { const fe = vecArgs(G).map(envFn); fnum = (p) => { const q = P(p), nn = crossN(partial(p, u), partial(p, v)); return fe.reduce((s, g, i) => s + g(q) * nn[i], 0); }; }
  else { const ge = envFn(G); fnum = (p) => ge(P(p)) * Math.hypot(...crossN(partial(p, u), partial(p, v))); }
  const lf = (t) => { const g = forEval(t); return (e) => evalR(g, e); };
  return {
    answers: valueAnswers(kind === "flux" ? "Flux" : "Surface integral", value),
    verify: () => TCV([valueCheck("quadrature", numOf(value), nestedQuad(fnum, [{ name: v, lo: lf(lim[2]), hi: lf(lim[3]) }, { name: u, lo: lf(lim[0]), hi: lf(lim[1]) }], { m: 12, panels: 6 }), "Gauss-Legendre quadrature over the parameter domain (finite-difference normal)")]),
  };
}

export const VECTOR = {
  div: cmdDiv, curl: cmdCurl, lineint: cmdLineint, conservative: cmdConservative, potential: cmdPotential,
  surfint: (n, e) => surfaceIntegral(n, e, "surfint"), flux: (n, e) => surfaceIntegral(n, e, "flux"),
};
void open; void probePoints; void sortVars;
