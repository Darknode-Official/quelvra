// Multiple integrals: iterated double / triple integrals over boxes and regions with variable
// limits, and integrals in polar, cylindrical and spherical coordinates.
//
// Solver: one exact definite integral per level (innermost first) with calc/int-definite.js.
// Verifier: nested Gauss-Legendre quadrature of the ORIGINAL integrand over the original region;
// for curvilinear coordinates the Jacobian factor is computed by finite differences of the
// coordinate map (never the symbolic r or rho^2 sin(phi) used by the solver).

import { definiteIntegral } from "../calc/int-definite.js";
import { X, toText, TCV, fail, safe, C, nice, tidyTrig, valueAnswers, dropAbs, regionPoints, envFn, forEval, evalR, nestedQuad, valueCheck, numOf, open } from "./util.js";

// levels: [{ v, lo, hi }] INNER first; f the integrand in the level variables
export function iterate(f, levels, env, what) {
  let cur = f;
  const inner = new Set();
  for (let i = 0; i < levels.length; i++) {
    const L = levels[i];
    env.checkTime && env.checkTime();
    // limits may depend only on OUTER variables
    for (const b of [L.lo, L.hi]) for (const s of X.freeSymbols(b)) {
      if (s === L.v || inner.has(s)) throw fail(`the limits of ${L.v} may only depend on the outer variables`);
    }
    cur = dropAbs(cur, regionPoints(levels.slice(i), levels.length - i > 2 ? 5 : 9));
    let r;
    try { r = definiteIntegral(cur, L.v, L.lo, L.hi, {}); } catch (e) {
      if (e && e.code === "TIMEOUT") throw e;
      throw fail(`the integral with respect to ${L.v} could not be evaluated exactly${e && e.message ? ` (${e.message})` : ""}`);
    }
    if (!r || r.status !== "exact") throw fail(`the integral with respect to ${L.v} has no closed form Quelvra can derive`);
    const nxt = tidyTrig(r.value);
    if (nxt === X.UNDEF || X.contains(nxt, X.UNDEF) || X.contains(nxt, X.OO)) throw fail("the integral diverges or is undefined");
    env.log.add({ rule: "multint.level", title: `Integrate with respect to ${L.v} from ${toText(L.lo)} to ${toText(L.hi)}`, why: i === 0 ? `Innermost integral; the other variables are constants.` : `Next integral outward.`, before: X.integral(cur, X.sym(L.v), L.lo, L.hi), after: nxt });
    cur = nxt;
    inner.add(L.v);
  }
  if (X.freeSymbols(cur).size) throw fail(`the ${what} still depends on ${[...X.freeSymbols(cur)].join(", ")}; check the order of the limits`);
  return cur;
}
const limFn = (u) => { const g = forEval(u); return (e) => evalR(g, e); };
function checkNested(value, g, levelsOuterFirst, what) {
  const want = numOf(value);
  if (!Number.isFinite(want)) return TCV([open("quadrature", "the value could not be evaluated")]);
  const ref = nestedQuad(g, levelsOuterFirst.map((L) => ({ name: L.v, lo: limFn(L.lo), hi: limFn(L.hi) })), { m: levelsOuterFirst.length === 3 ? 8 : 12, panels: levelsOuterFirst.length === 3 ? 4 : 6 });
  return TCV([valueCheck("quadrature", want, ref, `nested Gauss-Legendre ${what}`)]);
}
function levelsFrom(args, n, name) {
  if (args.length !== 1 + 3 * n) throw fail(`${name}(f, ${Array.from({ length: n }, (_, i) => `v${i + 1}, a${i + 1}, b${i + 1}`).join(", ")}): innermost variable first`);
  const levels = [];
  for (let i = 0; i < n; i++) {
    const v = args[1 + 3 * i];
    if (!v || v.k !== "sym") throw fail(`${name}: argument ${2 + 3 * i} must be a variable`);
    levels.push({ v: v.name, lo: C(args[2 + 3 * i]), hi: C(args[3 + 3 * i]) });
  }
  if (new Set(levels.map((l) => l.v)).size !== n) throw fail("each variable may appear only once");
  return levels;
}
function cartesian(node, env, n, name) {
  const f = node.args[0];
  if (!f || ["eq", "vector", "tuple", "matrix"].includes(f.k)) throw fail(`${name} needs an integrand`);
  const levels = levelsFrom(node.args, n, name);
  const extra = [...X.freeSymbols(f)].filter((s) => !levels.some((l) => l.v === s));
  if (extra.length) throw fail(`the integrand has symbols that are not integration variables (${extra.join(", ")})`);
  const value = nice(iterate(C(f), levels, env, `${name === "tplint" ? "triple" : "double"} integral`));
  const fe = envFn(f);
  return { answers: valueAnswers(`${n === 3 ? "Triple" : "Double"} integral`, value), verify: () => checkNested(value, fe, levels.slice().reverse(), "quadrature of the integrand") };
}
function cmdDbl(node, env) { return cartesian(node, env, 2, "dblint"); }
function cmdTpl(node, env) { return cartesian(node, env, 3, "tplint"); }

// integrate(integrate(f, x, a, b), y, c, d) [nested once more for triple]
export function nestedIntegral(node, env) {
  const levels = [];
  let cur = node;
  while (cur.k === "integral") {
    if (cur.args.length !== 4) throw fail("an iterated integral needs limits at every level");
    if (cur.args[1].k !== "sym") throw fail("integration variable expected");
    levels.unshift({ v: cur.args[1].name, lo: C(cur.args[2]), hi: C(cur.args[3]) });
    cur = cur.args[0];
  }
  if (levels.length < 2 || levels.length > 3) return null;
  const f = cur;
  const extra = [...X.freeSymbols(f)].filter((s) => !levels.some((l) => l.v === s));
  if (extra.length) throw fail(`the integrand has symbols that are not integration variables (${extra.join(", ")})`);
  // levels are INNER first after unshift of outer? cur walked outer -> inner, unshift puts inner first
  const value = nice(iterate(C(f), levels, env, "iterated integral"));
  const fe = envFn(f);
  return { answers: valueAnswers("Iterated integral", value), verify: () => checkNested(value, fe, levels.slice().reverse(), "quadrature of the integrand") };
}

// ------------------------------------------------------------------ curvilinear coordinates
const S = (n) => X.sym(n);
const MAPS = {
  polar: { vars: ["r", "theta"], coords: (r, t) => ({ x: X.mul(r, X.fn("cos", t)), y: X.mul(r, X.fn("sin", t)) }), jac: (r) => r, num: (p) => ({ x: p.r * Math.cos(p.theta), y: p.r * Math.sin(p.theta) }), jacText: "r" },
  cyl: { vars: ["r", "theta", "z"], coords: (r, t, z) => ({ x: X.mul(r, X.fn("cos", t)), y: X.mul(r, X.fn("sin", t)), z }), jac: (r) => r, num: (p) => ({ x: p.r * Math.cos(p.theta), y: p.r * Math.sin(p.theta), z: p.z }), jacText: "r" },
  sph: { vars: ["rho", "theta", "varphi"], coords: (rho, t, ph) => ({ x: X.mul(rho, X.fn("sin", ph), X.fn("cos", t)), y: X.mul(rho, X.fn("sin", ph), X.fn("sin", t)), z: X.mul(rho, X.fn("cos", ph)) }), jac: (rho, t, ph) => X.mul(X.pow(rho, X.TWO), X.fn("sin", ph)), num: (p) => ({ x: p.rho * Math.sin(p.varphi) * Math.cos(p.theta), y: p.rho * Math.sin(p.varphi) * Math.sin(p.theta), z: p.rho * Math.cos(p.varphi) }), jacText: "rho^2 sin(phi)" },
};
// |det| of the coordinate map's Jacobian by central differences
function fdJac(map, p) {
  const vs = map.vars, n = vs.length;
  const out = vs.map(() => []);
  const cart = n === 2 ? ["x", "y"] : ["x", "y", "z"];
  for (let j = 0; j < n; j++) {
    const h = 1e-5 * Math.max(1, Math.abs(p[vs[j]]));
    const a = map.num({ ...p, [vs[j]]: p[vs[j]] + h }), b = map.num({ ...p, [vs[j]]: p[vs[j]] - h });
    cart.forEach((c, i) => { out[i][j] = (a[c] - b[c]) / (2 * h); });
  }
  if (n === 2) return Math.abs(out[0][0] * out[1][1] - out[0][1] * out[1][0]);
  const m = out;
  return Math.abs(m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1]) - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0]) + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]));
}
function curvilinear(node, env, kind, name) {
  const map = MAPS[kind];
  const n = map.vars.length;
  const f0 = node.args[0];
  if (!f0 || node.args.length !== 1 + 2 * n) throw fail(`${name}(f, ${kind === "polar" ? "r1, r2, theta1, theta2" : kind === "cyl" ? "r1, r2, theta1, theta2, z1, z2" : "rho1, rho2, theta1, theta2, phi1, phi2"})`);
  let f = C(f0);
  if (kind === "sph" && X.hasSym(f, "phi")) f = X.subs(f, { phi: S("varphi") });
  const allowed = new Set([...map.vars, ...(kind === "polar" ? ["x", "y"] : ["x", "y", "z"])]);
  const extra = [...X.freeSymbols(f)].filter((s) => !allowed.has(s));
  if (extra.length) throw fail(`the integrand has symbols that are not coordinates (${extra.join(", ")})`);
  const bounds = [];
  for (let i = 0; i < n; i++) bounds.push({ lo: C(node.args[1 + 2 * i]), hi: C(node.args[2 + 2 * i]) });
  const fixPhi = (u) => (X.hasSym(u, "phi") ? X.subs(u, { phi: S("varphi") }) : u);
  bounds.forEach((b) => { b.lo = fixPhi(b.lo); b.hi = fixPhi(b.hi); });
  // integration order: polar r (inner), theta; cyl z (inner), r, theta; sph rho (inner), varphi, theta
  const order = kind === "polar" ? [0, 1] : kind === "cyl" ? [2, 0, 1] : [0, 2, 1];
  const levels = order.map((i) => ({ v: map.vars[i], lo: bounds[i].lo, hi: bounds[i].hi }));
  const cs = map.coords(...map.vars.map(S));
  const g = tidyTrig(X.mul(X.subs(f, cs), map.jac(...map.vars.map(S))));
  env.log.add({ rule: `multint.${kind}`, title: `Change to ${kind === "polar" ? "polar" : kind === "cyl" ? "cylindrical" : "spherical"} coordinates`, why: `Substitute ${Object.entries(cs).map(([k, v]) => `${k} = ${toText(v)}`).join(", ")} and multiply by the Jacobian ${map.jacText}.`, before: f, after: g });
  const value = nice(iterate(g, levels, env, "integral"));
  // verifier: ORIGINAL f composed with the numeric coordinate map, times a finite-difference Jacobian
  const fe = envFn(f);
  const integrand = (p) => { const c = map.num(p); return fe({ ...p, ...c }) * fdJac(map, p); };
  return { answers: valueAnswers("Integral", value), verify: () => checkNested(value, integrand, levels.slice().reverse(), `quadrature (finite-difference Jacobian of the coordinate map)`) };
}
export const MULTINT = {
  dblint: cmdDbl, tplint: cmdTpl,
  polarint: (n, e) => curvilinear(n, e, "polar", "polarint"),
  cylint: (n, e) => curvilinear(n, e, "cyl", "cylint"),
  sphint: (n, e) => curvilinear(n, e, "sph", "sphint"),
};
void safe;
