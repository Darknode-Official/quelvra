// PDE basics: verify a proposed solution, classify second-order linear PDEs in two variables, and
// solve the heat and wave equations on 0 < x < L with zero (Dirichlet) boundary values by Fourier
// sine series.
//
// Notation: u_x, u_xx, u_xy, u_t, u_tt ... are the partial derivatives of u.
//   pdecheck(u, equation)          does u satisfy the equation?
//   classifypde(equation)          B^2 - 4AC for A u_xx + B u_xy + C u_yy + (lower order) = 0
//   heat(f, x, t, L, k)            u_t = k u_xx, u(0, t) = u(L, t) = 0, u(x, 0) = f(x)
//   wave(f, g, x, t, L, c)         u_tt = c^2 u_xx, u = 0 at x = 0, L, u(x, 0) = f, u_t(x, 0) = g
//
// Verification (independent of the solver):
//   pdecheck   : "true" from an exact zero residual, checked by finite differences of u; "false"
//                from an exact nonzero residual value at a rational point, confirmed by finite
//                differences there
//   classify   : the coefficients re-extracted numerically (evaluating the equation with unit
//                derivative values) at sample points, sign of B^2 - 4AC compared with the claim
//   heat, wave : the finite solution (or the first terms of the series) satisfies the PDE and
//                both boundary conditions EXACTLY (symbolic substitution), the finite solution also
//                the initial conditions exactly; series coefficients b_n (n = 1..8) are compared
//                with Gauss-Legendre quadrature of the initial data

import { definiteIntegral } from "../calc/int-definite.js";
import { breakpoints, restrict, integerTrig, linearIn } from "./transforms.js";
import {
  X, toText, TCV, fail, safe, pass, bad, open, fmt, C, D, nice, tidyTrig, isZeroExact, expand,
  evalR, forEval, envFn, fdPartial, probePoints, closeTo, quad1, numOf,
} from "./util.js";
import { makeCtx } from "../simplify.js";

const S = X.sym;
const ctx = () => makeCtx({ budget: { ops: 600000 } });
const DER = /^u_([a-z]+)$/;
const zeroT = (u) => isZeroExact(u) === true || isZeroExact(tidyTrig(u)) === true;

// derivative symbols u_<vars> in a tree: Map name -> [vars]
function derivSyms(u) {
  const out = new Map();
  const walk = (w) => { if (w.k === "sym") { const m = w.name.match(DER); if (m) out.set(w.name, [...m[1]]); } for (const a of w.args || []) walk(a); };
  walk(u);
  return out;
}
const residualOf = (eq) => {
  if (!eq || eq.k !== "eq") throw fail("give the equation with an = sign, for example u_t = u_xx");
  return C(X.sub(eq.args[0], eq.args[1]));
};

// ------------------------------------------------------------------ pdecheck
function cmdPdecheck(node, env) {
  const [u0, eq] = node.args;
  if (!u0 || ["eq", "rel", "vector", "matrix"].includes(u0.k)) throw fail("pdecheck(u, equation), for example pdecheck(e^(-t) sin(x), u_t = u_xx)");
  const u = C(u0.k === "eq" && u0.args[0].k === "sym" && u0.args[0].name === "u" ? u0.args[1] : u0);
  const R = residualOf(eq);
  const ds = derivSyms(R);
  if (!ds.size) throw fail("the equation has no partial derivatives u_x, u_t, ...");
  const vars = [...new Set([...X.freeSymbols(u), ...[...ds.values()].flat()])].sort();
  const bad1 = [...X.freeSymbols(R)].filter((s) => s !== "u" && !ds.has(s) && !vars.includes(s));
  if (bad1.length) throw fail(`the equation has unknown symbols (${bad1.join(", ")})`);
  const sub = { u };
  for (const [name, vs] of ds) { let d = u; for (const v of vs) d = D(d, v); sub[name] = C(d); }
  const res = tidyTrig(C(X.subs(R, sub)));
  env.log.add({ rule: "pde.check", title: "Substitute u into the equation", why: [...ds.keys()].map((k) => `${k} = ${toText(sub[k])}`).join(", ") + `; left side minus right side = ${toText(res)}.`, before: eq, after: res });
  // numeric residual by finite differences of the ORIGINAL u (verifier)
  const ue = envFn(u);
  const Rf = forEval(R);
  const numRes = (p) => {
    const e = { ...p, u: ue(p) };
    let scale = Math.abs(e.u);
    for (const [name, vs] of ds) { e[name] = fdPartial(ue, p, vs); scale = Math.max(scale, Math.abs(e[name])); }
    return { v: evalR(Rf, e), scale: Math.max(1, scale) };
  };
  if (zeroT(res)) {
    return {
      answers: [{ kind: "exact", label: "Satisfies the equation", tree: X.TRUE }],
      verify: () => {
        let good = 0;
        for (const p of probePoints(vars, 18, 5, -1.3, 1.4)) {
          if (good >= 6) break;
          const { v, scale } = numRes(p);
          if (!Number.isFinite(v)) continue;
          if (Math.abs(v) > 1e-5 * scale) return TCV([bad("finite-differences", `at ${fmtP(p)} the finite-difference residual is ${fmt(v)}`)]);
          good++;
        }
        return TCV([good >= 3 ? pass("finite-differences", `the residual computed from finite differences of u vanishes (to rounding) at ${good} random points`) : open("finite-differences", "too few points")]);
      },
    };
  }
  // look for an exact witness point where the residual is nonzero
  const cand = [[1, 2], [1, 3], [2, 1], [1, 1], [3, 2], [2, 5]].map((q) => Object.fromEntries(vars.map((v, i) => [v, X.num(q[i % 2] + i, q[(i + 1) % 2] + 1)])));
  for (const pt of cand) {
    const val = safe(() => C(X.subs(res, pt)));
    if (!val) continue;
    const vv = numOf(val);
    if (!Number.isFinite(vv) || Math.abs(vv) < 1e-6) continue;
    const pn = Object.fromEntries(Object.entries(pt).map(([k, w]) => [k, numOf(w)]));
    return {
      answers: [{ kind: "exact", label: "Satisfies the equation", tree: X.FALSE }, { kind: "exact", label: "residual (left side minus right side)", tree: res }],
      verify: () => {
        const { v, scale } = numRes(pn);
        if (!Number.isFinite(v)) return TCV([open("finite-differences", "the residual could not be evaluated")]);
        return TCV([Math.abs(v) > 1e-4 * scale && closeTo(v, vv, 1e-4) ? pass("finite-differences", `at ${fmtP(pn)} the residual is ${fmt(vv)} (exact) and ${fmt(v)} by finite differences of u, not 0`) : bad("finite-differences", `the finite-difference residual at ${fmtP(pn)} is ${fmt(v)}, the exact residual is ${fmt(vv)}`)]);
      },
    };
  }
  throw fail("could not decide whether the residual is zero");
}
const fmtP = (p) => Object.entries(p).map(([k, v]) => `${k} = ${fmt(v)}`).join(", ");

// ------------------------------------------------------------------ classify
function cmdClassify(node, env) {
  const eq = node.args[0];
  const R = residualOf(eq);
  const ds = derivSyms(R);
  const second = [...ds.entries()].filter(([, vs]) => vs.length === 2);
  if (!second.length) throw fail("the equation has no second-order derivatives u_xx, u_xy, u_yy");
  if ([...ds.values()].some((vs) => vs.length > 2)) throw fail("only second-order equations are classified");
  const vars = [...new Set(second.flatMap(([, vs]) => vs))];
  if (vars.length === 1) {
    const other = [...new Set([...ds.values()].flat())].filter((v) => v !== vars[0]);
    if (other.length !== 1) throw fail("classification needs two independent variables");
    vars.push(other[0]);
  }
  if (vars.length !== 2) throw fail("classification is for equations in two variables");
  const [a, b] = vars;
  const names = [...ds.keys(), "u"];
  // linear in u and its derivatives, and the second-order coefficients free of them
  for (const n1 of names) for (const n2 of names) if (!zeroT(D(D(R, n1), n2))) throw fail("the equation is not linear in u and its derivatives");
  const coef = (vs) => { const ks = second.filter(([, w]) => w.slice().sort().join("") === vs.slice().sort().join("")).map(([k]) => D(R, k)); return ks.length ? C(X.add(...ks)) : X.ZERO; };
  const A = coef([a, a]), B = coef([a, b]), Cc = coef([b, b]);
  const allowed = new Set(vars);
  for (const k of [A, B, Cc]) for (const s of X.freeSymbols(k)) if (!allowed.has(s)) throw fail(`the coefficients may only depend on ${a} and ${b}`);
  const disc = nice(C(X.sub(X.pow(B, X.TWO), X.mul(X.num(4), A, Cc))));
  env.log.add({ rule: "pde.classify", title: "Discriminant", why: `A = ${toText(A)} (u_${a}${a}), B = ${toText(B)} (u_${a}${b}), C = ${toText(Cc)} (u_${b}${b}); B^2 - 4AC = ${toText(disc)}. Positive: hyperbolic, zero: parabolic, negative: elliptic.`, before: eq, after: disc });
  // verifier: numeric coefficient extraction from the ORIGINAL equation
  const Rf = forEval(R);
  const base = Object.fromEntries(names.map((k) => [k, 0]));
  const numCoef = (p, set) => { const e0 = { ...p, ...base }; const e1 = { ...e0 }; for (const k of set) e1[k] = 1; return evalR(Rf, e1) - evalR(Rf, e0); };
  const kA = second.filter(([, w]) => w[0] === a && w[1] === a).map(([k]) => k), kC = second.filter(([, w]) => w[0] === b && w[1] === b).map(([k]) => k), kB = second.filter(([, w]) => w[0] !== w[1]).map(([k]) => k);
  const numDisc = (p) => {
    const nA = kA.length ? numCoef(p, kA.slice(0, 1)) : 0, nC = kC.length ? numCoef(p, kC.slice(0, 1)) : 0;
    // B is the sum of the coefficients of u_ab and u_ba: set both to 1
    const nB = kB.length ? numCoef(p, kB) : 0;
    return nB * nB - 4 * nA * nC;
  };
  const kindOf = (v) => (v > 1e-9 ? "hyperbolic" : v < -1e-9 ? "elliptic" : "parabolic");
  if (!X.freeSymbols(disc).size) {
    const dv = numOf(disc);
    const type = X.isNum(disc) ? (disc.v.n > 0n ? "hyperbolic" : disc.v.n < 0n ? "elliptic" : "parabolic") : kindOf(dv);
    return {
      answers: [{ kind: "exact", label: "Type", tree: S(type) }, { kind: "exact", label: "B^2 - 4AC", tree: disc }],
      verify: () => {
        const p = { [a]: 0.37, [b]: -0.53 };
        const nd = numDisc(p);
        return TCV([Number.isFinite(nd) && kindOf(nd) === type && closeTo(nd, dv, 1e-9) ? pass("coefficients", `coefficients re-extracted numerically from the equation give B^2 - 4AC = ${fmt(nd)}`) : bad("coefficients", `numeric coefficients give B^2 - 4AC = ${fmt(nd)}`)]);
      },
    };
  }
  // variable coefficients: regions
  const vs = [...X.freeSymbols(disc)];
  let sets;
  const li = vs.length === 1 ? linearIn(disc, vs[0]) : null;
  if (li && !X.freeSymbols(li.k).size && isZeroExact(li.k) === false) {
    const v = S(vs[0]), root = C(X.div(X.neg(li.c), li.k));
    const up = numOf(li.k) > 0;
    sets = { hyperbolic: X.rel(up ? ">" : "<", v, root), elliptic: X.rel(up ? "<" : ">", v, root), parabolic: X.eq(v, root) };
  } else {
    sets = { hyperbolic: X.rel(">", disc, X.ZERO), elliptic: X.rel("<", disc, X.ZERO), parabolic: X.eq(disc, X.ZERO) };
  }
  return {
    answers: [
      { kind: "exact", label: "B^2 - 4AC", tree: disc },
      ...["hyperbolic", "parabolic", "elliptic"].map((k) => ({ kind: "set", label: k, tree: sets[k] })),
    ],
    verify: () => {
      const g = [-2, -1, -0.5, 0, 0.5, 1, 2];
      for (const xv of g) for (const yv of g) {
        const p = { [a]: xv, [b]: yv };
        const nd = numDisc(p);
        if (!Number.isFinite(nd)) continue;
        const want = kindOf(nd);
        const got = ["hyperbolic", "parabolic", "elliptic"].filter((k) => evalTruth(sets[k], p));
        if (got.length !== 1 || got[0] !== want) return TCV([bad("coefficients", `at ${fmtP(p)} the numeric B^2 - 4AC = ${fmt(nd)} (${want}) but the regions give ${got.join(", ") || "none"}`)]);
      }
      return TCV([pass("coefficients", "on a 7 x 7 grid the numerically re-extracted B^2 - 4AC has the sign each region claims")]);
    },
  };
}
function evalTruth(r, p) {
  const l = evalR(forEval(r.args[0]), p), rr = evalR(forEval(r.args[1]), p);
  if (r.k === "eq") return Math.abs(l - rr) <= 1e-12;
  return r.op === ">" ? l > rr + 1e-12 : r.op === "<" ? l < rr - 1e-12 : r.op === ">=" ? l >= rr - 1e-12 : l <= rr + 1e-12;
}

// ------------------------------------------------------------------ Fourier sine coefficients on (0, L)
// finite: f = sum c_m sin(m pi x / L)  -> Map m -> c ; general: b_n = (2/L) int_0^L f sin(n pi x/L) dx
function finiteSine(f, x, L) {
  const e = C(expand(C(f), ctx()));
  if (e === X.ZERO) return new Map();
  const terms = e.k === "add" ? e.args : [e];
  const out = new Map();
  for (const t of terms) {
    const fs = t.k === "mul" ? t.args : [t];
    const sins = fs.filter((w) => w.k === "fn" && w.name === "sin" && X.hasSym(w, x));
    const rest = fs.filter((w) => !sins.includes(w));
    if (sins.length !== 1 || rest.some((w) => X.hasSym(w, x))) return null;
    const m = C(X.div(sins[0].args[0], X.div(X.mul(X.PI, S(x)), L)));
    if (!X.isInt(m) || m.v.n <= 0n) return null;
    const k = Number(m.v.n);
    out.set(k, C(X.add(out.get(k) || X.ZERO, X.mul(...rest, X.ONE))));
  }
  return out;
}
function sineCoef(f, x, L, env) {
  const Ln = numOf(L);
  const bps = breakpoints(f, x, 0, Ln);
  const cuts = [X.ZERO, ...bps.map(([, r]) => r), L];
  const n = S("n");
  const kernel = X.fn("sin", C(X.div(X.mul(n, X.PI, S(x)), L)));
  let total = X.ZERO;
  for (let i = 0; i + 1 < cuts.length; i++) {
    const mid = (numOf(cuts[i]) + numOf(cuts[i + 1])) / 2;
    const piece = restrict(f, x, mid);
    if (piece === X.UNDEF || X.contains(piece, X.UNDEF)) throw fail("the initial data are not defined on all of (0, L)");
    let r;
    try { r = definiteIntegral(C(X.mul(piece, kernel)), x, cuts[i], cuts[i + 1], {}); } catch (e) { if (e && e.code === "TIMEOUT") throw e; throw fail("a Fourier sine coefficient integral could not be evaluated"); }
    if (!r || r.status !== "exact") throw fail("a Fourier sine coefficient has no closed form Quelvra can derive");
    total = X.add(total, r.value);
  }
  const bn = nice(integerTrig(C(X.mul(X.div(X.TWO, L), total)), "n"));
  for (let k = 1; k <= 8; k++) { const v = numOf(C(X.subs(bn, { n: X.num(k) }))); if (!Number.isFinite(v)) throw fail(`the general coefficient formula breaks down at n = ${k} (not supported)`); }
  env.log.add({ rule: "pde.sine-coefficients", title: "Fourier sine coefficients", why: `b_n = (2/L) integral from 0 to L of f(${x}) sin(n pi ${x}/L) d${x} with L = ${toText(L)}; sin(n pi) = 0 and cos(n pi) = (-1)^n.`, before: f, after: bn });
  return { bn, cutsN: cuts.map(numOf) };
}
// numeric (2/L) int_0^L f sin(k pi x/L) dx
function numSine(f, x, Ln, cutsN, k) {
  const fe = envFn(f);
  let s = 0, err = 0;
  for (let i = 0; i + 1 < cutsN.length; i++) {
    const r = quad1((u) => fe({ [x]: u }) * Math.sin((k * Math.PI * u) / Ln), cutsN[i], cutsN[i + 1], { m: 16, panels: 8 });
    if (!r.ok) return { ok: false };
    s += r.value; err += r.err;
  }
  return { ok: true, value: (2 * s) / Ln, err: (2 * err) / Ln };
}

function boundaryArgs(node, name, withG) {
  const k = withG ? 1 : 0;
  const f = node.args[0], g = withG ? node.args[1] : null;
  const xv = node.args[1 + k], tv = node.args[2 + k], Lv = node.args[3 + k], cv = node.args[4 + k];
  if (!f || !xv || xv.k !== "sym" || !tv || tv.k !== "sym" || !Lv) throw fail(withG ? "wave(f, g, x, t, L, c): u_tt = c^2 u_xx on 0 < x < L, u = 0 at both ends, u(x, 0) = f, u_t(x, 0) = g" : "heat(f, x, t, L, k): u_t = k u_xx on 0 < x < L, u = 0 at both ends, u(x, 0) = f");
  const x = xv.name, t = tv.name;
  const L = C(Lv), K = cv ? C(cv) : X.ONE;
  for (const [w, what] of [[L, "L"], [K, withG ? "c" : "k"]]) { if (X.freeSymbols(w).size || !(numOf(w) > 0)) throw fail(`${what} must be a positive number`); }
  for (const h of [f, g].filter(Boolean)) {
    const extra = [...X.freeSymbols(h)].filter((v) => v !== x);
    if (extra.length) throw fail(`the initial data may only depend on ${x}`);
  }
  if (node.args.length > 5 + k) throw fail(`too many arguments for ${name}`);
  return { f: C(f), g: g ? C(g) : null, x, t, L, K };
}
// exact checks of a candidate u: PDE and both boundary conditions
function exactChecks(u, pdeRes, x, L, label) {
  const checks = [];
  checks.push(zeroT(pdeRes(u)) ? pass("exact-pde", `${label} satisfies the PDE exactly (symbolic substitution)`, false) : bad("exact-pde", `${label} does not satisfy the PDE`));
  const b0 = C(X.subs(u, { [x]: X.ZERO })), bL = integerTrig(C(X.subs(u, { [x]: L })), "n");
  checks.push(zeroT(b0) && zeroT(bL) ? pass("exact-boundary", `${label} vanishes at ${x} = 0 and ${x} = ${toText(L)}`, false) : bad("exact-boundary", `${label} does not vanish at the ends`));
  return checks;
}

// ------------------------------------------------------------------ heat
function cmdHeat(node, env) {
  const { f, x, t, L, K } = boundaryArgs(node, "heat", false);
  const X_ = S(x), T_ = S(t), n = S("n");
  const mode = (m) => X.fn("sin", C(X.div(X.mul(m, X.PI, X_), L)));
  const decay = (m) => X.pow(X.E, C(X.neg(X.mul(K, X.pow(X.div(X.mul(m, X.PI), L), X.TWO), T_))));
  const pdeRes = (u) => C(X.sub(D(u, t), X.mul(K, D(D(u, x), x))));
  const fin = finiteSine(f, x, L);
  env.log.add({ rule: "pde.heat", title: "Separation of variables", why: `u = sum b_n e^(-k (n pi/L)^2 t) sin(n pi x/L) solves u_t = k u_xx with u = 0 at x = 0 and x = L (k = ${toText(K)}, L = ${toText(L)}); b_n are the sine coefficients of u(x, 0).`, before: f, after: null, kind: "note" });
  if (fin) {
    const u = tidyTrig(C(X.add(X.ZERO, ...[...fin].map(([m, c]) => X.mul(c, decay(X.num(m)), mode(X.num(m)))))));
    return {
      answers: [{ kind: "exact", label: "u(x, t)", tree: u }],
      verify: () => {
        const cs = exactChecks(u, pdeRes, x, L, "u");
        cs.push(zeroT(C(X.sub(C(X.subs(u, { [t]: X.ZERO })), f))) ? pass("exact-initial", "u(x, 0) = f(x) exactly", false) : bad("exact-initial", "u(x, 0) differs from f"));
        return TCV(cs);
      },
    };
  }
  const { bn, cutsN } = sineCoef(f, x, L, env);
  const u = X.sum(nice(X.mul(bn, decay(n), mode(n))), n, X.ONE, X.OO);
  return {
    answers: [{ kind: "exact", label: "bn", tree: bn }, { kind: "exact", label: "u(x, t)", tree: u, note: "Fourier sine series" }],
    verify: () => TCV([...termChecks([bn], (k, cs) => C(X.mul(cs[0], decay(X.num(k)), mode(X.num(k)))), pdeRes, x, L), ...coefChecks(bn, f, null, x, L, cutsN, "b_n")]),
  };
}
// shared series verification: the first four terms exactly, coefficients 1..8 by quadrature (records)
function termChecks(coefs, termAt, pdeRes, x, L) {
  for (let k = 1; k <= 4; k++) {
    const cs = coefs.map((c) => C(X.subs(c, { n: X.num(k) })));
    const r = exactChecks(termAt(k, cs), pdeRes, x, L, `term n = ${k}`);
    if (r.some((c) => c.status === "failed")) return r;
  }
  return [pass("exact-terms", "the terms n = 1..4 satisfy the PDE and both boundary conditions exactly", false)];
}
function coefChecks(c, data, scale, x, L, cutsN, what) {
  const Ln = numOf(L);
  for (let k = 1; k <= 8; k++) {
    const claim = numOf(C(X.subs(c, { n: X.num(k) }))) * (scale ? scale(k) : 1);
    const ref = numSine(data, x, Ln, cutsN, k);
    if (!ref.ok) return [open("quadrature", "the numeric coefficient did not converge")];
    if (!(Math.abs(claim - ref.value) <= Math.max(1e-9, 20 * ref.err))) return [bad("quadrature", `${what} for n = ${k}: quadrature gives ${fmt(ref.value)}, the formula gives ${fmt(claim)}`)];
  }
  return [pass("quadrature", `${what} for n = 1..8 agree with Gauss-Legendre quadrature of the initial data`)];
}

// ------------------------------------------------------------------ wave
function cmdWave(node, env) {
  const { f, g, x, t, L, K } = boundaryArgs(node, "wave", true);
  const X_ = S(x), T_ = S(t), n = S("n");
  const w = (m) => C(X.div(X.mul(m, X.PI, K), L));
  const mode = (m) => X.fn("sin", C(X.div(X.mul(m, X.PI, X_), L)));
  const pdeRes = (u) => C(X.sub(D(D(u, t), t), X.mul(X.pow(K, X.TWO), D(D(u, x), x))));
  env.log.add({ rule: "pde.wave", title: "Separation of variables", why: `u = sum (a_n cos(n pi c t/L) + b_n sin(n pi c t/L)) sin(n pi x/L) with a_n the sine coefficients of f and b_n = L/(n pi c) times the sine coefficients of g (c = ${toText(K)}, L = ${toText(L)}).`, before: X.tuple(f, g), after: null, kind: "note" });
  const ff = finiteSine(f, x, L), gf = finiteSine(g, x, L);
  if (ff && gf) {
    const parts = [];
    for (const [m, c] of ff) parts.push(X.mul(c, X.fn("cos", X.mul(w(X.num(m)), T_)), mode(X.num(m))));
    for (const [m, c] of gf) parts.push(X.mul(c, X.recip(w(X.num(m))), X.fn("sin", X.mul(w(X.num(m)), T_)), mode(X.num(m))));
    const u = tidyTrig(C(X.add(X.ZERO, ...parts)));
    return {
      answers: [{ kind: "exact", label: "u(x, t)", tree: u }],
      verify: () => {
        const cs = exactChecks(u, pdeRes, x, L, "u");
        cs.push(zeroT(C(X.sub(C(X.subs(u, { [t]: X.ZERO })), f))) ? pass("exact-initial", "u(x, 0) = f(x) exactly", false) : bad("exact-initial", "u(x, 0) differs from f"));
        cs.push(zeroT(C(X.sub(C(X.subs(D(u, t), { [t]: X.ZERO })), g))) ? pass("exact-initial", "u_t(x, 0) = g(x) exactly", false) : bad("exact-initial", "u_t(x, 0) differs from g"));
        return TCV(cs);
      },
    };
  }
  // general series (a finite part that is identically zero is allowed)
  const general = (h, which) => {
    if (h === X.ZERO || C(h) === X.ZERO) return { c: X.ZERO, cutsN: null, zero: true };
    const fs = finiteSine(h, x, L);
    if (fs) throw fail(`mixing a finite sine sum for ${which} with a general series for the other initial condition is not supported`);
    const r = sineCoef(h, x, L, env);
    return { c: r.bn, cutsN: r.cutsN };
  };
  const A = general(f, "f"), G = general(g, "g");
  const an = A.c;
  const bn = G.zero ? X.ZERO : nice(C(X.mul(G.c, X.recip(w(n)))));
  const u = X.sum(nice(X.mul(X.add(X.mul(an, X.fn("cos", X.mul(w(n), T_))), X.mul(bn, X.fn("sin", X.mul(w(n), T_)))), mode(n))), n, X.ONE, X.OO);
  return {
    answers: [{ kind: "exact", label: "an", tree: an }, { kind: "exact", label: "bn", tree: bn }, { kind: "exact", label: "u(x, t)", tree: u, note: "Fourier sine series" }],
    verify: () => {
      const recs = termChecks([an, bn], (k, cs) => C(X.mul(X.add(X.mul(cs[0], X.fn("cos", X.mul(w(X.num(k)), T_))), X.mul(cs[1], X.fn("sin", X.mul(w(X.num(k)), T_)))), mode(X.num(k)))), pdeRes, x, L);
      if (!A.zero) recs.push(...coefChecks(an, f, null, x, L, A.cutsN, "a_n"));
      if (!G.zero) recs.push(...coefChecks(bn, g, (k) => numOf(w(X.num(k))), x, L, G.cutsN, "b_n (times n pi c/L)"));
      return TCV(recs);
    },
  };
}
export const PDE = { pdecheck: cmdPdecheck, classifypde: cmdClassify, heat: cmdHeat, wave: cmdWave };
void safe; void closeTo;
