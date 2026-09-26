// Multivariable differential calculus: partial derivatives, gradient, directional derivative,
// Jacobian, Hessian, Laplacian, total differential, tangent planes, critical points with the
// second-derivative test, and Lagrange multipliers.
//
// Verification (independent of the symbolic differentiator): nested central differences of the
// ORIGINAL function at random points; first-order contact of tangent planes from function values
// only; sampling around critical points; multistart Newton searches for missed critical points;
// sampling of the constraint set for claimed constrained maxima / minima.

import { solve as orchestrate } from "../orchestrate.js";
import {
  X, Q, toText, TCV, fail, safe, pass, bad, open, fmt, C, D, nice, isZeroExact, isVec, vecArgs, isSymVec, sortVars, varsOf,
  constArg, exprArg, tidyTrig, valueAnswers, evalR, forEval, envFn, fdPartial, probePoints, probeCheck, closeTo, fmtEnv, newtonSystem, linSolve, signConst, cmpConst,
} from "./util.js";

const STD = ["x", "y", "z", "t", "u", "v", "w"];
const label = (seq) => (seq.every((v) => v.length === 1) ? `f_${seq.join("")}` : `partial derivative (${seq.join(", ")})`);
const tolFor = (k) => [0, 2e-6, 1e-5, 1e-4, 5e-4][k] || 1e-3;

// ---------------------------------------------------------------- partial derivatives
function cmdPdiff(node, env) {
  const [f0, ...rest] = node.args;
  const f = exprArg(f0, "pdiff needs a function");
  const seq = [];
  for (const a of rest) {
    if (a.k === "sym") seq.push(a.name);
    else if (isSymVec(a)) seq.push(...a.args.map((s) => s.name));
    else if (X.isInt(a) && seq.length && a.v.n >= 1n && a.v.n <= 8n) { for (let i = 1; i < Number(a.v.n); i++) seq.push(seq[seq.length - 1]); }
    else throw fail("pdiff(f, x, y, ...) takes the variables in the order of differentiation");
  }
  if (!seq.length) throw fail("pdiff needs the variables, for example pdiff(f, x, y)");
  if (seq.length > 6) throw fail("at most 6 differentiations");
  let cur = f;
  for (const v of seq) {
    const nxt = nice(D(cur, v));
    env.log.add({ rule: "multivar.partial", title: `Differentiate with respect to ${v}`, why: `Treat every other variable as a constant.`, before: X.deriv(cur, X.sym(v)), after: nxt });
    cur = nxt;
  }
  const names = sortVars(new Set([...X.freeSymbols(f), ...seq]));
  return {
    answers: [{ kind: "exact", label: label(seq), tree: cur }],
    verify: () => (seq.length > 4 ? TCV([open("finite-differences", "order too high for a numerical check")]) :
      TCV([probeCheck("finite-differences", names, (p) => evalR(forEval(cur), p), (p) => fdPartial(envFn(f), p, seq), { tol: tolFor(seq.length), what: `derivative ${label(seq)}` })])),
  };
}

// argument layout: f, [vars]?, then numeric vectors
function splitArgs(args, name) {
  const f = exprArg(args[0], `${name} needs a function`);
  let i = 1, vars = null;
  const vecs = [];
  if (args[i] && isSymVec(args[i])) {
    // a vector of plain symbols is the variable list when it names variables of f (or more vectors follow)
    const names = args[i].args.map((a) => a.name);
    if (names.some((n) => X.hasSym(f, n)) || args.length > 2) { vars = args[i]; i++; }
  }
  for (; i < args.length; i++) {
    if (!isVec(args[i])) throw fail(`${name}: expected a vector, got ${toText(args[i])}`);
    vecs.push(args[i]);
  }
  return { f, vars, vecs };
}
const pointOf = (vec, n, what) => {
  const a = vecArgs(vec);
  if (!a || a.length !== n) throw fail(`${what} must have ${n} coordinates`);
  return a.map((c, i) => constArg(c, `coordinate ${i + 1} of ${what}`));
};
const subsPt = (u, vars, pt) => { const m = {}; vars.forEach((v, i) => { m[v] = pt[i].tree; }); return nice(X.subs(u, m)); };
const numEnv = (vars, pt) => { const e = {}; vars.forEach((v, i) => { e[v] = pt[i].v; }); return e; };

function cmdGrad(node, env) {
  const { f, vars: vv, vecs } = splitArgs(node.args, "grad");
  const vars = varsOf([f], vv);
  const comps = vars.map((v) => nice(D(f, v)));
  env.log.add({ rule: "multivar.gradient", title: "Gradient", why: `grad f = (${vars.map((v) => `df/d${v}`).join(", ")}).`, before: f, after: X.vector(...comps) });
  if (vecs.length > 1) throw fail("grad(f, [vars], [point])");
  if (vecs.length === 1) {
    const pt = pointOf(vecs[0], vars.length, "the point");
    const at = comps.map((c) => subsPt(c, vars, pt));
    if (at.some((c) => c === X.UNDEF || X.contains(c, X.UNDEF) || X.freeSymbols(c).size)) throw fail("the gradient is not defined at that point");
    const e = numEnv(vars, pt);
    return {
      answers: [{ kind: "exact", label: `grad f at (${pt.map((p) => toText(p.tree)).join(", ")})`, tree: X.vector(...at) }],
      verify: () => TCV(at.map((c, i) => { const n = fdPartial(envFn(f), e, [vars[i]]), cv = evalR(forEval(c), {}); return closeTo(cv, n, 2e-6) ? pass("finite-differences", `d f/d${vars[i]} = ${fmt(n)} numerically`) : Number.isFinite(n) ? bad("finite-differences", `d f/d${vars[i]} is ${fmt(n)} numerically, not ${fmt(cv)}`) : open("finite-differences", "f could not be evaluated near the point"); })),
    };
  }
  return {
    answers: [{ kind: "exact", label: "grad f", tree: X.vector(...comps) }],
    verify: () => TCV(comps.map((c, i) => probeCheck("finite-differences", vars, (p) => evalR(forEval(c), p), (p) => fdPartial(envFn(f), p, [vars[i]]), { tol: 2e-6, what: `d f/d${vars[i]}` }))),
  };
}

function cmdDirderiv(node, env) {
  const { f, vars: vv, vecs } = splitArgs(node.args, "dirderiv");
  if (!vecs.length || vecs.length > 2) throw fail("dirderiv(f, direction) or dirderiv(f, direction, point)");
  const vars = varsOf([f], vv);
  const u = vecArgs(vecs[0]);
  if (u.length !== vars.length) throw fail(`the direction must have ${vars.length} components (variables ${vars.join(", ")})`);
  const uc = u.map((c, i) => constArg(c, `direction component ${i + 1}`));
  const len = nice(X.sqrt(X.add(...uc.map((c) => X.pow(c.tree, X.TWO)))));
  const lv = Math.hypot(...uc.map((c) => c.v));
  if (!(lv > 0)) throw fail("the direction must be a nonzero vector");
  const g = vars.map((v) => nice(D(f, v)));
  let Du = nice(X.div(X.add(...g.map((gi, i) => X.mul(gi, uc[i].tree))), len));
  env.log.add({ rule: "multivar.directional", title: "Directional derivative", why: `D_u f = grad f . u/|u| with grad f = (${g.map(toText).join(", ")}) and |u| = ${toText(len)}.`, before: f, after: Du });
  const unit = uc.map((c) => c.v / lv);
  const numDir = (p) => {
    const h0 = 1e-3;
    const at = (h) => { const e = { ...p }; vars.forEach((v, i) => { e[v] = p[v] + h * unit[i]; }); return evalR(forEval(f), e); };
    const cd = (h) => (at(h) - at(-h)) / (2 * h);
    return (4 * cd(h0 / 2) - cd(h0)) / 3;
  };
  if (vecs.length === 2) {
    const pt = pointOf(vecs[1], vars.length, "the point");
    Du = subsPt(Du, vars, pt);
    if (X.freeSymbols(Du).size || X.contains(Du, X.UNDEF)) throw fail("the directional derivative is not defined at that point");
    const e = numEnv(vars, pt);
    return {
      answers: valueAnswers("directional derivative", Du),
      verify: () => { const n = numDir(e), c = evalR(forEval(Du), {}); return TCV([closeTo(c, n, 2e-6) ? pass("difference-quotient", `(f(p + h u) - f(p - h u))/(2h) -> ${fmt(n)}`) : bad("difference-quotient", `the difference quotient along u gives ${fmt(n)}, not ${fmt(c)}`)]); },
    };
  }
  return {
    answers: [{ kind: "exact", label: "directional derivative", tree: Du }],
    verify: () => TCV([probeCheck("difference-quotient", vars, (p) => evalR(forEval(Du), p), numDir, { tol: 2e-6, what: "directional derivative" })]),
  };
}

function jacobianParts(node, name) {
  const F = vecArgs(node.args[0]);
  if (!F) throw fail(`${name} needs a vector of functions, for example ${name}([x^2 y, x + y], [x, y])`);
  const vars = varsOf(F, node.args[1]);
  return { F, vars, J: F.map((fi) => vars.map((v) => nice(D(fi, v)))) };
}
const matNode = (M) => X.matrix(M.map((r) => X.tuple(...r)));
function checkMatrix(kind, vars, M, numEntry, tol = 2e-6) {
  const out = [];
  M.forEach((row, i) => row.forEach((e, j) => out.push(probeCheck(kind, vars, (p) => evalR(forEval(e), p), (p) => numEntry(p, i, j), { tol, what: `entry (${i + 1}, ${j + 1})` }))));
  return out;
}
function cmdJacobian(node, env) {
  const { F, vars, J } = jacobianParts(node, "jacobian");
  env.log.add({ rule: "multivar.jacobian", title: "Jacobian matrix", why: `Row i holds the partial derivatives of component i with respect to ${vars.join(", ")}.`, before: X.vector(...F), after: matNode(J) });
  const names = sortVars(new Set([...vars, ...F.flatMap((f) => [...X.freeSymbols(f)])]));
  return { answers: [{ kind: "exact", label: "Jacobian", tree: matNode(J) }], verify: () => TCV(checkMatrix("finite-differences", names, J, (p, i, j) => fdPartial(envFn(F[i]), p, [vars[j]]))) };
}
function det(M) {
  const n = M.length;
  if (n === 1) return M[0][0];
  if (n === 2) return X.sub(X.mul(M[0][0], M[1][1]), X.mul(M[0][1], M[1][0]));
  const terms = [];
  for (let j = 0; j < n; j++) {
    const minor = M.slice(1).map((r) => r.filter((_, k) => k !== j));
    terms.push(X.mul(j % 2 ? X.NEG_ONE : X.ONE, M[0][j], det(minor)));
  }
  return X.add(...terms);
}
function numDet(A) {
  const n = A.length, M = A.map((r) => r.slice());
  let d = 1;
  for (let c = 0; c < n; c++) {
    let p = c;
    for (let r = c + 1; r < n; r++) if (Math.abs(M[r][c]) > Math.abs(M[p][c])) p = r;
    if (M[p][c] === 0) return 0;
    if (p !== c) { [M[p], M[c]] = [M[c], M[p]]; d = -d; }
    d *= M[c][c];
    for (let r = c + 1; r < n; r++) { const f = M[r][c] / M[c][c]; for (let k = c; k < n; k++) M[r][k] -= f * M[c][k]; }
  }
  return d;
}
function cmdJacobianDet(node, env) {
  const { F, vars, J } = jacobianParts(node, "jacobiandet");
  if (F.length !== vars.length) throw fail("the Jacobian determinant needs as many functions as variables");
  if (F.length > 4) throw fail("at most 4 variables");
  const d = nice(safe(() => C(det(J))) || det(J));
  const dt = safe(() => tidyTrig(d)) || d;
  env.log.add({ rule: "multivar.jacobiandet", title: "Jacobian determinant", why: "Determinant of the Jacobian matrix.", before: matNode(J), after: dt });
  const names = sortVars(new Set([...vars, ...F.flatMap((f) => [...X.freeSymbols(f)])]));
  return {
    answers: valueAnswers("Jacobian determinant", dt),
    verify: () => TCV([probeCheck("finite-differences", names, (p) => evalR(forEval(dt), p), (p) => numDet(F.map((fi) => vars.map((v) => fdPartial(envFn(fi), p, [v])))), { tol: 1e-5, what: "determinant" })]),
  };
}

function cmdHessian(node, env) {
  const f = exprArg(node.args[0], "hessian needs a function");
  const vars = varsOf([f], node.args[1], { min: 1 });
  const H = vars.map((a) => vars.map((b) => nice(D(D(f, a), b))));
  env.log.add({ rule: "multivar.hessian", title: "Hessian matrix", why: "Entry (i, j) is the second partial derivative with respect to the i-th and j-th variables.", before: f, after: matNode(H) });
  return { answers: [{ kind: "exact", label: "Hessian", tree: matNode(H) }], verify: () => TCV(checkMatrix("finite-differences", vars, H, (p, i, j) => fdPartial(envFn(f), p, [vars[i], vars[j]]), 1e-5)) };
}
function cmdLaplacian(node, env) {
  const f = exprArg(node.args[0], "laplacian needs a function");
  const vars = varsOf([f], node.args[1]);
  const L = nice(X.add(...vars.map((v) => D(D(f, v), v))));
  env.log.add({ rule: "multivar.laplacian", title: "Laplacian", why: `Sum of the second derivatives in ${vars.join(", ")}.`, before: f, after: L });
  return { answers: [{ kind: "exact", label: "Laplacian", tree: L }], verify: () => TCV([probeCheck("finite-differences", vars, (p) => evalR(forEval(L), p), (p) => vars.reduce((s, v) => s + fdPartial(envFn(f), p, [v, v]), 0), { tol: 1e-5, what: "Laplacian" })]) };
}
function cmdTotaldiff(node, env) {
  const f = exprArg(node.args[0], "totaldiff needs a function");
  const vars = varsOf([f], node.args[1]);
  const g = vars.map((v) => nice(D(f, v)));
  const df = X.add(...g.map((gi, i) => X.mul(gi, X.sym("d" + vars[i]))));
  env.log.add({ rule: "multivar.differential", title: "Total differential", why: `df = ${vars.map((v) => `f_${v} d${v}`).join(" + ")}.`, before: f, after: df });
  return { answers: [{ kind: "exact", label: "df", tree: df }], verify: () => TCV(g.map((gi, i) => probeCheck("finite-differences", vars, (p) => evalR(forEval(gi), p), (p) => fdPartial(envFn(f), p, [vars[i]]), { tol: 2e-6, what: `coefficient of d${vars[i]}` }))) };
}

// ---------------------------------------------------------------- tangent planes
function primitive(ns) {
  // scale a rational normal vector to coprime integers, first nonzero positive
  if (!ns.every((n) => X.isNum(n))) return ns;
  let L = 1n;
  const gcd = (a, b) => { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) [a, b] = [b, a % b]; return a; };
  for (const n of ns) L = (L * n.v.d) / gcd(L, n.v.d);
  let ints = ns.map((n) => (n.v.n * L) / n.v.d);
  let g = 0n;
  for (const k of ints) g = gcd(g, k);
  if (g === 0n) return ns;
  ints = ints.map((k) => k / g);
  const first = ints.find((k) => k !== 0n);
  if (first < 0n) ints = ints.map((k) => -k);
  return ints.map((k) => X.num(Q.Q(k)));
}
function cmdTangentPlane(node, env) {
  const args = node.args;
  let F = args[0];
  if (!F) throw fail("tangentplane(f, point)");
  let vv = null, ptv;
  if (args.length === 3) { vv = args[1]; ptv = args[2]; } else if (args.length === 2) ptv = args[1]; else throw fail("tangentplane(f, point) or tangentplane(f, [vars], point)");
  if (!isVec(ptv)) throw fail("the point must be a vector such as [1, 2]");
  // graph z = f(x, y)
  let graph = null;
  if (F.k === "eq" && F.args[0].k === "sym" && X.freeOf(F.args[1], F.args[0])) graph = { z: F.args[0].name, f: F.args[1] };
  else if (F.k !== "eq") {
    const vs = varsOf([F], vv);
    if (vs.length === 2 && (ptv.args.length === 2 || ptv.args.length === 3)) graph = { z: vs.includes("z") ? "w" : "z", f: F };
    else if (vs.length === 3 && ptv.args.length === 3) F = X.eq(F, X.subs(F, Object.fromEntries(vs.map((v, i) => [v, ptv.args[i]]))));
  }
  if (graph) {
    const vars = varsOf([graph.f], vv);
    if (vars.length !== 2) throw fail("a tangent plane to a graph z = f(x, y) needs a function of two variables");
    const pt = pointOf(X.vector(...ptv.args.slice(0, 2)), 2, "the point");
    const z0 = subsPt(graph.f, vars, pt);
    if (X.freeSymbols(z0).size || X.contains(z0, X.UNDEF)) throw fail("f is not defined at that point");
    if (ptv.args.length === 3 && isZeroExact(X.sub(ptv.args[2], z0)) !== true) throw fail(`the point is not on the surface: f(${toText(pt[0].tree)}, ${toText(pt[1].tree)}) = ${toText(z0)}`);
    const g = vars.map((v) => subsPt(D(graph.f, v), vars, pt));
    if (g.some((c) => X.freeSymbols(c).size || X.contains(c, X.UNDEF))) throw fail("f is not differentiable at that point");
    const plane = nice(X.add(z0, ...g.map((gi, i) => X.mul(gi, X.sub(X.sym(vars[i]), pt[i].tree)))));
    env.log.add({ rule: "multivar.tangentplane", title: "Tangent plane to a graph", why: `z = f(a, b) + f_${vars[0]}(a, b)(${vars[0]} - a) + f_${vars[1]}(a, b)(${vars[1]} - b) with f(a, b) = ${toText(z0)}, f_${vars[0]} = ${toText(g[0])}, f_${vars[1]} = ${toText(g[1])}.`, before: graph.f, after: plane });
    const tree = X.eq(X.sym(graph.z), plane);
    return {
      answers: [{ kind: "exact", label: "Tangent plane", tree }],
      verify: () => {
        // first-order contact from function values only: f - plane = O(h^2) in every direction
        const fe = envFn(graph.f), pe = envFn(plane);
        const p0 = numEnv(vars, pt);
        let worst = 0, n = 0;
        for (let k = 0; k < 12; k++) {
          const a = (2 * Math.PI * k) / 12 + 0.3;
          const e = (h) => { const q = { [vars[0]]: p0[vars[0]] + h * Math.cos(a), [vars[1]]: p0[vars[1]] + h * Math.sin(a) }; return fe(q) - pe(q); };
          const e1 = e(2e-3), e2 = e(1e-3);
          if (!Number.isFinite(e1) || !Number.isFinite(e2)) continue;
          n++;
          if (Math.abs(e1) > 1e-11) worst = Math.max(worst, Math.abs(e2) / Math.abs(e1));
          if (Math.abs(e2) > 1e-4) worst = Math.max(worst, 1);
        }
        if (n < 8) return TCV([open("contact", "f could not be evaluated around the point")]);
        const onSurface = Math.abs(fe(p0) - pe(p0)) <= 1e-9 * Math.max(1, Math.abs(fe(p0)));
        return TCV([onSurface && worst < 0.35 ? pass("contact", "the plane passes through the point and f - plane shrinks like h^2 in 12 directions (first-order contact)") : bad("contact", "the plane does not touch the surface to first order")]);
      },
    };
  }
  // level surface G(x, y, z) = 0
  if (F.k !== "eq") throw fail("give the surface as an equation, for example x^2 + y^2 + z^2 = 14");
  const G = C(X.sub(F.args[0], F.args[1]));
  const vars = varsOf([G], vv);
  if (vars.length !== 3) throw fail("a level surface needs three variables");
  const pt = pointOf(ptv, 3, "the point");
  if (isZeroExact(subsPt(G, vars, pt)) !== true) throw fail("the point is not on the surface");
  let nrm = vars.map((v) => subsPt(D(G, v), vars, pt));
  if (nrm.some((c) => X.freeSymbols(c).size || X.contains(c, X.UNDEF))) throw fail("the surface is not differentiable at that point");
  if (nrm.every((c) => isZeroExact(c) === true)) throw fail("the gradient vanishes at that point, so the tangent plane is not determined");
  nrm = primitive(nrm.map(C));
  const lhs = nice(X.add(...nrm.map((c, i) => X.mul(c, X.sym(vars[i])))));
  const rhs = nice(X.add(...nrm.map((c, i) => X.mul(c, pt[i].tree))));
  env.log.add({ rule: "multivar.tangentplane.level", title: "Tangent plane to a level surface", why: `The gradient of G = ${toText(G)} is normal to the surface; at the point it is proportional to (${nrm.map(toText).join(", ")}).`, before: F, after: X.eq(lhs, rhs) });
  return {
    answers: [{ kind: "exact", label: "Tangent plane", tree: X.eq(lhs, rhs) }],
    verify: () => {
      const p0 = numEnv(vars, pt);
      const g = vars.map((v) => fdPartial(envFn(G), p0, [v]));
      const n = nrm.map((c) => evalR(forEval(c), {}));
      if (!g.every(Number.isFinite)) return TCV([open("normal", "G could not be differentiated numerically at the point")]);
      const gl = Math.hypot(...g), nl = Math.hypot(...n);
      const cross = Math.hypot(g[1] * n[2] - g[2] * n[1], g[2] * n[0] - g[0] * n[2], g[0] * n[1] - g[1] * n[0]) / (gl * nl);
      const through = Math.abs(evalR(forEval(X.sub(lhs, rhs)), p0)) < 1e-9 * Math.max(1, Math.abs(evalR(forEval(rhs), {})));
      return TCV([cross < 1e-6 && through ? pass("normal", "the plane passes through the point and its normal is parallel to the numerical gradient of G") : bad("normal", "the plane's normal is not parallel to the gradient of G")]);
    },
  };
}

// ---------------------------------------------------------------- critical points
function solveSystem(eqs, env, unknowns) {
  const r = orchestrate(X.system(...eqs), { timeLimit: Math.max(1500, Math.min(8000, (env.deadline || Date.now() + 8000) - Date.now() - 500)), crossCheck: false, variable: unknowns });
  if (r.noSolution) return { points: [], complete: true };
  if (!r.ok || !r.verification || r.verification.status !== "passed") return null;
  const pts = [];
  for (const a of r.answers) {
    if (a.kind !== "solution") return null;
    const m = new Map(a.values.map(([k, v]) => [k, v]));
    if (!unknowns.every((u) => m.has(u))) return null;
    const vals = unknowns.map((u) => C(m.get(u)));
    if (vals.some((v) => X.freeSymbols(v).size || X.contains(v, X.UNDEF))) return null;
    const nums = vals.map((v) => evalR(forEval(v), {}));
    if (!nums.every(Number.isFinite)) continue; // complex solution: not a real point
    pts.push({ vals, nums });
  }
  return { points: pts, complete: true };
}
const isStdVar = (s) => STD.includes(s);
export function multivarCriticalApplies(node) {
  const f0 = node.args[0];
  if (!f0 || node.args.length > 2) return false;
  let f = f0;
  if (f.k === "eq" && f.args[0].k === "sym") f = f.args[1];
  if (["eq", "rel", "system", "vector", "tuple", "matrix"].includes(f.k)) return false;
  const fs = [...X.freeSymbols(f)];
  return fs.length >= 2 && fs.every(isStdVar);
}
// leading principal minors -> classification
function classify(H) {
  const n = H.length;
  const minors = [];
  for (let k = 1; k <= n; k++) minors.push(nice(det(H.slice(0, k).map((r) => r.slice(0, k)))));
  const signs = minors.map((m) => safe(() => signConst(m)));
  if (signs.some((s) => s === null || s === undefined)) return { type: "undecided", minors };
  if (signs[n - 1] === 0) return { type: "inconclusive", minors, signs };
  if (signs.every((s) => s > 0)) return { type: "min", minors, signs };
  if (signs.every((s, i) => (i % 2 === 0 ? s < 0 : s > 0))) return { type: "max", minors, signs };
  return { type: "saddle", minors, signs };
}
const TYPE_LABEL = { min: "local minimum", max: "local maximum", saddle: "saddle point", inconclusive: "second-derivative test inconclusive" };
export function multivarCritical(node, env) {
  let f = node.args[0];
  if (f.k === "eq" && f.args[0].k === "sym") f = f.args[1];
  const vars = sortVars(X.freeSymbols(f));
  if (vars.length > 4) throw fail("at most 4 variables");
  const g = vars.map((v) => nice(D(f, v)));
  env.log.add({ rule: "multivar.critical.gradient", title: "Set the gradient to zero", why: `Critical points solve ${g.map((gi) => `${toText(gi)} = 0`).join(", ")}.`, before: f, after: X.vector(...g) });
  const sol = solveSystem(g.map((gi) => X.eq(gi, X.ZERO)), env, vars);
  if (!sol) throw fail("the system grad f = 0 could not be solved completely (it may have infinitely many solutions)");
  const H = vars.map((a) => vars.map((b) => nice(D(D(f, a), b))));
  const answers = [], info = [];
  for (const p of sol.points) {
    const m = {}; vars.forEach((v, i) => { m[v] = p.vals[i]; });
    const Hp = H.map((r) => r.map((e) => nice(X.subs(e, m))));
    const cl = classify(Hp);
    if (cl.type === "undecided") throw fail("the sign of the Hessian determinant at a critical point could not be decided");
    const fv = nice(X.subs(f, m));
    info.push({ p, type: cl.type });
    env.log.add({ rule: "multivar.critical.test", title: `Second-derivative test at (${p.vals.map(toText).join(", ")})`, why: `Leading principal minors of the Hessian: ${cl.minors.map(toText).join(", ")}; ${TYPE_LABEL[cl.type]}.`, before: matNode(Hp), after: null, kind: "note" });
    answers.push({ kind: "solution", label: TYPE_LABEL[cl.type], values: [...vars.map((v, i) => [v, p.vals[i]]), ["f", fv]] });
  }
  if (!answers.length) answers.push({ kind: "none", label: "No critical points (grad f = 0 has no real solution)", proof: "the gradient system has no real solution" });
  const fe = envFn(f);
  return {
    answers, noSolution: !sol.points.length,
    verify: () => {
      const checks = [];
      for (const { p, type } of info) {
        const e = {}; vars.forEach((v, i) => { e[v] = p.nums[i]; });
        const gn = vars.map((v) => fdPartial(fe, e, [v]));
        const sc = Math.max(1, Math.abs(fe(e)));
        if (!gn.every((x) => Number.isFinite(x) && Math.abs(x) < 1e-6 * sc)) { checks.push(bad("gradient", `the numerical gradient at (${p.nums.map(fmt).join(", ")}) is not zero`)); continue; }
        if (type === "inconclusive") continue;
        // sample f on small spheres around the point
        let up = 0, down = 0;
        const f0 = fe(e);
        for (const eps of [1e-2, 3e-3]) for (let k = 0; k < 48; k++) {
          const dir = vars.map((_, i) => Math.sin(1.3 + k * (0.7 + 0.37 * i) + i * i));
          const L = Math.hypot(...dir);
          const q = { ...e }; vars.forEach((v, i) => { q[v] = e[v] + (eps * dir[i]) / L; });
          const d = fe(q) - f0;
          if (d > 1e-13 * sc) up++; else if (d < -1e-13 * sc) down++;
        }
        const ok = type === "min" ? down === 0 && up > 80 : type === "max" ? up === 0 && down > 80 : up > 0 && down > 0;
        checks.push(ok ? pass("sampling", `f sampled on small spheres around (${p.nums.map(fmt).join(", ")}) behaves like a ${TYPE_LABEL[type]}`) : bad("sampling", `f near (${p.nums.map(fmt).join(", ")}) does not behave like a ${TYPE_LABEL[type]}`));
      }
      // multistart Newton on the numerical gradient: every critical point it finds must be listed
      const G = (xs) => { const e = {}; vars.forEach((v, i) => { e[v] = xs[i]; }); return vars.map((v) => fdPartial(fe, e, [v])); };
      const grid = vars.length <= 2 ? [-3.1, -1.7, -0.6, 0.45, 1.3, 2.2, 3.4] : vars.length === 3 ? [-2.3, -0.7, 0.55, 1.9] : [-1.6, 0.4, 1.7];
      let starts = [[]];
      for (let i = 0; i < vars.length; i++) starts = starts.flatMap((s) => grid.map((gv) => [...s, gv + 0.01 * i]));
      let found = 0;
      for (const s of starts) {
        const r = newtonSystem(G, s, { tol: 1e-10 });
        if (!r || r.some((v) => Math.abs(v) > 1e3)) continue;
        found++;
        if (!info.some(({ p }) => p.nums.every((v, i) => Math.abs(v - r[i]) < 2e-3 * Math.max(1, Math.abs(v))))) return TCV([...checks, bad("completeness", `a Newton search found another critical point near (${r.map(fmt).join(", ")})`)]);
      }
      checks.push(found || !info.length ? pass("completeness", `multistart Newton search (${starts.length} starts) found no critical point missing from the list`) : open("completeness", "the Newton search did not converge"));
      if (!info.length) checks.push(pass("no-critical-points", "no Newton start converged to a critical point"));
      return TCV(checks);
    },
  };
}

// ---------------------------------------------------------------- Lagrange multipliers
function isDefinite(Hc) {
  const n = Hc.length;
  const s = [];
  for (let k = 1; k <= n; k++) s.push(safe(() => signConst(nice(det(Hc.slice(0, k).map((r) => r.slice(0, k)))))));
  if (s.some((v) => v === null || v === undefined)) return false;
  return s.every((v) => v > 0) || s.every((v, i) => (i % 2 === 0 ? v < 0 : v > 0));
}
function compactConstraint(g, vars) {
  // polynomial of degree <= 2 with a constant definite Hessian: every level set is bounded
  const H = vars.map((a) => vars.map((b) => nice(D(D(g, a), b))));
  if (H.some((r) => r.some((e) => X.freeSymbols(e).size))) return false;
  const third = vars.every((a) => vars.every((b) => vars.every((c) => isZeroExact(D(D(D(g, a), b), c)) === true)));
  return third && isDefinite(H);
}
function cmdLagrange(node, env) {
  const args = node.args;
  const f = exprArg(args[0], "lagrange needs a function");
  let cons = args[1];
  if (!cons) throw fail("lagrange(f, g = c) or lagrange(f, [g1 = c1, g2 = c2])");
  const list = isVec(cons) ? cons.args : cons.k === "system" ? cons.args : [cons];
  if (!list.every((c) => c.k === "eq")) throw fail("constraints must be equations, for example x^2 + y^2 = 1");
  const gs = list.map((c) => C(X.sub(c.args[0], c.args[1])));
  const vars = varsOf([f, ...gs], args[2]);
  if (vars.length < 2 || vars.length > 4) throw fail("lagrange works with 2 to 4 variables");
  if (gs.length >= vars.length) throw fail("too many constraints");
  const lams = gs.length === 1 ? ["lambda"] : gs.map((_, i) => `lambda${i + 1}`);
  const eqs = [];
  vars.forEach((v) => eqs.push(X.eq(nice(X.sub(D(f, v), X.add(...gs.map((g, i) => X.mul(X.sym(lams[i]), D(g, v)))))), X.ZERO)));
  gs.forEach((g) => eqs.push(X.eq(g, X.ZERO)));
  env.log.add({ rule: "multivar.lagrange.system", title: "Lagrange conditions", why: `grad f = ${lams.join(" grad g + ")} grad g together with the constraint${gs.length > 1 ? "s" : ""}.`, before: f, after: X.system(...eqs) });
  const sol = solveSystem(eqs, env, [...vars, ...lams]);
  if (!sol) throw fail("the Lagrange system could not be solved completely");
  // points where the constraint gradients are dependent (single constraint: grad g = 0 on g = 0)
  let singular = [];
  if (gs.length === 1) {
    const s2 = solveSystem([X.eq(gs[0], X.ZERO), ...vars.map((v) => X.eq(nice(D(gs[0], v)), X.ZERO))], env, vars);
    if (!s2) throw fail("could not decide whether the constraint has singular points");
    singular = s2.points;
  } else throw fail("more than one constraint is not supported yet");
  const cands = [];
  const seen = (nums) => cands.some((c) => c.nums.every((v, i) => Math.abs(v - nums[i]) < 1e-10 * Math.max(1, Math.abs(v))));
  for (const p of sol.points) { const nums = p.nums.slice(0, vars.length); if (!seen(nums)) cands.push({ vals: p.vals.slice(0, vars.length), nums, lam: p.vals.slice(vars.length) }); }
  for (const p of singular) if (!seen(p.nums)) cands.push({ vals: p.vals, nums: p.nums, lam: null, singular: true });
  if (!cands.length) throw fail("the constraint set has no candidate points (it may be empty)");
  for (const c of cands) { const m = {}; vars.forEach((v, i) => { m[v] = c.vals[i]; }); c.f = nice(X.subs(f, m)); c.fv = evalR(forEval(c.f), {}); }
  if (cands.some((c) => !Number.isFinite(c.fv))) throw fail("f is not defined at a candidate point");
  const compact = gs.some((g) => compactConstraint(g, vars));
  let mx = null, mn = null;
  if (compact) {
    const byV = [...cands].sort((a, b) => a.fv - b.fv);
    mn = byV[0]; mx = byV[byV.length - 1];
    for (const c of cands) {
      c.isMax = isZeroExact(X.sub(c.f, mx.f)) === true || Math.abs(c.fv - mx.fv) < 1e-12 * Math.max(1, Math.abs(mx.fv)) && isZeroExact(X.sub(c.f, mx.f)) !== false;
      c.isMin = isZeroExact(X.sub(c.f, mn.f)) === true || Math.abs(c.fv - mn.fv) < 1e-12 * Math.max(1, Math.abs(mn.fv)) && isZeroExact(X.sub(c.f, mn.f)) !== false;
    }
  }
  const answers = cands.map((c) => ({
    kind: "solution", label: c.singular ? "candidate (singular point of the constraint)" : compact ? (c.isMax && c.isMin ? "maximum and minimum" : c.isMax ? "maximum" : c.isMin ? "minimum" : "candidate") : "candidate",
    values: [...vars.map((v, i) => [v, c.vals[i]]), ...(c.lam ? lams.map((l, i) => [l, c.lam[i]]) : []), ["f", c.f]],
  }));
  if (compact) {
    answers.push({ kind: "exact", label: "Maximum value", tree: mx.f }, { kind: "exact", label: "Minimum value", tree: mn.f });
    env.log.add({ rule: "multivar.lagrange.compare", title: "Compare the candidates", why: "The constraint set is closed and bounded (its quadratic part is definite), so f attains a maximum and a minimum there, at candidate points.", before: null, after: null, kind: "note" });
  } else env.log.add({ rule: "multivar.lagrange.unbounded", title: "Candidates only", why: "The constraint set is not known to be bounded, so these are the candidates for extrema; Quelvra does not claim a global maximum or minimum.", before: null, after: null, kind: "note" });
  const fe = envFn(f), ge = gs.map(envFn);
  return {
    answers,
    verify: () => {
      const checks = [];
      for (const c of cands) {
        const e = {}; vars.forEach((v, i) => { e[v] = c.nums[i]; });
        const gv = ge.map((g) => g(e));
        if (!gv.every((x) => Math.abs(x) < 1e-9)) { checks.push(bad("constraint", `(${c.nums.map(fmt).join(", ")}) is not on the constraint`)); continue; }
        const gf = vars.map((v) => fdPartial(fe, e, [v]));
        const gg = vars.map((v) => fdPartial(ge[0], e, [v]));
        if (c.singular) { checks.push(gg.every((x) => Math.abs(x) < 1e-6) ? pass("singular", "grad g vanishes there") : bad("singular", "grad g does not vanish at the singular candidate")); continue; }
        const lam = evalR(forEval(c.lam[0]), {});
        const ok = gf.every((x, i) => closeTo(x, lam * gg[i], 1e-6));
        checks.push(ok ? pass("lagrange-condition", `grad f = lambda grad g holds numerically at (${c.nums.map(fmt).join(", ")})`) : bad("lagrange-condition", `grad f != lambda grad g at (${c.nums.map(fmt).join(", ")})`));
      }
      // multistart Newton on the Lagrange system (finite-difference gradients)
      const Fs = (xs) => { const e = {}; vars.forEach((v, i) => { e[v] = xs[i]; }); const lam = xs[vars.length]; return [...vars.map((v) => fdPartial(fe, e, [v]) - lam * fdPartial(ge[0], e, [v])), ge[0](e)]; };
      const grid = vars.length === 2 ? [-2.6, -1.1, 0.35, 1.4, 2.7] : [-1.9, 0.3, 1.6];
      let starts = [[]];
      for (let i = 0; i < vars.length; i++) starts = starts.flatMap((s) => grid.map((gv) => [...s, gv + 0.013 * i]));
      starts = starts.flatMap((s) => [-1.7, 0.6, 2.3].map((l) => [...s, l]));
      for (const s of starts) {
        const r = newtonSystem(Fs, s, { tol: 1e-10 });
        if (!r || r.some((v) => Math.abs(v) > 1e3)) continue;
        if (!cands.some((c) => c.nums.every((v, i) => Math.abs(v - r[i]) < 2e-3 * Math.max(1, Math.abs(v))))) return TCV([...checks, bad("completeness", `a Newton search found another Lagrange point near (${r.slice(0, vars.length).map(fmt).join(", ")})`)]);
      }
      checks.push(pass("completeness", `multistart Newton search (${starts.length} starts) found no Lagrange point missing from the list`));
      if (compact) {
        // sample the constraint set: project random points onto g = 0 along grad g
        let n = 0, over = null;
        for (const p of probePoints(vars, 400, 11, -3, 3)) {
          let xs = vars.map((v) => p[v]);
          for (let it = 0; it < 60; it++) {
            const e = {}; vars.forEach((v, i) => { e[v] = xs[i]; });
            const gval = ge[0](e);
            if (!Number.isFinite(gval)) { xs = null; break; }
            if (Math.abs(gval) < 1e-12) break;
            const gr = vars.map((v) => fdPartial(ge[0], e, [v]));
            const g2 = gr.reduce((s, x) => s + x * x, 0);
            if (!(g2 > 1e-20)) { xs = null; break; }
            xs = xs.map((x, i) => x - (gval * gr[i]) / g2);
          }
          if (!xs) continue;
          const e = {}; vars.forEach((v, i) => { e[v] = xs[i]; });
          if (Math.abs(ge[0](e)) > 1e-10) continue;
          const fv = fe(e);
          if (!Number.isFinite(fv)) continue;
          n++;
          if (fv > mx.fv + 1e-8 * Math.max(1, Math.abs(mx.fv)) || fv < mn.fv - 1e-8 * Math.max(1, Math.abs(mn.fv))) { over = { e, fv }; break; }
        }
        if (over) checks.push(bad("sampling", `f = ${fmt(over.fv)} at ${fmtEnv(over.e)} on the constraint lies outside [min, max]`));
        else checks.push(n >= 50 ? pass("sampling", `${n} sampled points of the constraint set give values between the claimed minimum and maximum`) : open("sampling", "too few points of the constraint set could be sampled"));
      }
      return TCV(checks);
    },
  };
}

export const MULTIVAR = {
  pdiff: cmdPdiff, grad: cmdGrad, dirderiv: cmdDirderiv, jacobian: cmdJacobian, jacobiandet: cmdJacobianDet, hessian: cmdHessian,
  laplacian: cmdLaplacian, totaldiff: cmdTotaldiff, tangentplane: cmdTangentPlane, lagrange: cmdLagrange,
};
export { det as symDet, matNode, numDet, solveSystem };
void cmpConst; void linSolve; void valueAnswers;
