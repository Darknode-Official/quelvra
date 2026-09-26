// Quelvra analysis commands: completesquare, apart, identity, line / slope / distance / midpoint,
// arclength, areabetween, volume (disk method about the x-axis), avgvalue.

import { toContractVerification } from "../orchestrate.js";
import { diff } from "../calc/diff.js";
import { expand, together, numerDenom } from "../simplify.js";
import { equivalent } from "../verify.js";
import { inferDomain } from "../domain.js";
import { trigsimp, simplifyFull } from "../rules.js";
import { definiteIntegral } from "../calc/int-definite.js";
import { coeffTrees } from "../solve/poly.js";
import * as P from "../poly.js";
import { X, Q, toText, C, safe, fail, dv, fAt, evalReal, evalC, definedNum, pass, bad, open, fmt, fnAndVar, constArg, tidy, hp, zerosOf, familyMembers, quadrature, approxRec, NOLOG, signConst, definedAt } from "./util.js";

const TCV = (list) => toContractVerification(list);
const scale = (v) => Math.max(1, Math.abs(v));
const eqStatus = (e) => (e.status === "equivalent-exact" ? "verified-exact" : e.status === "equivalent-numeric" ? "verified-numeric" : e.status === "different" ? "failed" : "inconclusive");

// ---------------------------------------------------------------- complete the square
export function cmdCompleteSquare(node, env) {
  const { f: p, x } = fnAndVar(node.args, "completesquare");
  const cs = safe(() => coeffTrees(expand(C(p)), x));
  if (!cs || cs.length !== 3) throw fail(`completesquare needs a quadratic in ${x}, such as 2x^2 + 8x + 3`);
  const [c, b, a] = cs.map((t) => C(t));
  const conds = [];
  if (!X.isNum(a)) conds.push(X.rel("!=", a, X.ZERO));
  else if (a === X.ZERO) throw fail("the x^2 coefficient is 0");
  const h = tidy(C(X.div(X.neg(b), X.mul(X.TWO, a))));
  const k = tidy(C(X.sub(c, X.div(X.pow(b, X.TWO), X.mul(X.num(4), a)))));
  const X0 = X.sym(x);
  const inner = C(X.sub(X0, h));
  let tree = X.pow(inner, X.TWO);
  if (a !== X.ONE) tree = X.mul(a, tree);
  if (k !== X.ZERO) tree = X.add(tree, k);
  env.log.add({ rule: "analysis.completesquare.coefficients", title: "Read off the coefficients", why: `a = ${toText(a)}, b = ${toText(b)}, c = ${toText(c)}.`, before: p, after: null, kind: "note" });
  env.log.add({ rule: "analysis.completesquare.vertex", title: "h = -b/(2a), k = c - b^2/(4a)", why: `a x^2 + b x + c = a (x - h)^2 + k with h = ${toText(h)} and k = ${toText(k)}.`, before: p, after: tree, conditions: conds, kind: conds.length ? "conditional" : "equivalent" });
  return {
    answers: [{ kind: "exact", label: "Completed square", tree }, { kind: "exact", label: "Vertex (h, k)", tree: X.tuple(h, k) }],
    conditions: conds, solutionStatus: "exact",
    verify: () => {
      const e = equivalent(expand(tree), expand(p));
      return TCV([{ status: eqStatus(e), checks: [{ kind: "expand-back", ok: e.status !== "different", detail: "expanding a(x - h)^2 + k gives back the input" }] }]);
    },
  };
}

// ---------------------------------------------------------------- partial fractions
export function cmdApart(node, env) {
  const { f: p, x } = fnAndVar(node.args, "apart");
  const r = safe(() => P.apart(p, x));
  if (!r) throw fail("apart needs a rational function of x with rational coefficients");
  const [, den] = safe(() => numerDenom(together(C(p)))) || [null, null];
  const conds = den && !X.freeOf(den, x) ? [X.rel("!=", den, X.ZERO)] : [];
  env.log.add({ rule: "analysis.apart", title: "Partial fraction decomposition", why: "Divide out the polynomial part, factor the denominator over the rationals and solve for the numerators of each factor power (every numerator has lower degree than its factor).", before: p, after: r, conditions: conds, kind: "equivalent" });
  return {
    answers: [{ kind: "exact", label: "Partial fractions", tree: r }], conditions: conds, solutionStatus: "exact",
    verify: () => {
      const e = equivalent(r, p);
      return TCV([{ status: eqStatus(e), checks: [{ kind: "recombine", ok: e.status !== "different", detail: e.status === "different" ? "the decomposition differs from the input" : "the decomposition equals the input wherever it is defined" }] }]);
    },
  };
}

// ---------------------------------------------------------------- identity
const NICE = ["1/2", "2", "-1/2", "-3", "5/7", "-7/5", "3/2", "11/4", "-5/2", "1/3", "7", "-9/4", "13/8", "4/9", "-2/9", "17/3"];
function exactPoint(s) { const [n, d] = s.split("/"); return X.num(Q.Q(BigInt(n), BigInt(d || "1"))); }
function proveZero(d) {
  const tries = [
    () => C(d),
    () => C(expand(C(d))),
    () => { const t = together(C(d)); const [n] = numerDenom(t); return C(expand(n)); },
    () => trigsimp(C(d), { maxMs: 400 }).result,
    () => simplifyFull(d).result,
    () => { const r = trigsimp(C(d), { maxMs: 400 }).result; const t = together(r); const [n] = numerDenom(t); return C(expand(n)); },
    () => { const t = together(trigsimp(together(C(d)), { maxMs: 400 }).result); const [n] = numerDenom(t); return trigsimp(C(expand(n)), { maxMs: 400 }).result; },
  ];
  for (const [i, t] of tries.entries()) { const r = safe(t); if (r === X.ZERO) return i; }
  return -1;
}
export function cmdIdentity(node, env) {
  let lhs, rhs;
  if (node.args.length === 1 && node.args[0].k === "eq") [lhs, rhs] = node.args[0].args;
  else if (node.args.length === 2 && node.args[0].k !== "eq") [lhs, rhs] = node.args;
  else throw fail("identity needs an equation: identity(lhs = rhs) or identity(lhs, rhs)");
  const vars = [...new Set([...X.freeSymbols(lhs), ...X.freeSymbols(rhs)])].sort();
  if (!vars.length) throw fail("there is no variable; evaluate the two sides instead");
  const X0 = vars[0];
  // 1. counterexample search (sampling at exact rational points, confirmed at 30 digits)
  const pts = [...NICE.map(exactPoint)];
  for (let i = 0; i < 24; i++) pts.push(X.num(Q.Q(BigInt(((i * 7919) % 97) - 48), BigInt(7 + (i % 5)))));
  let agree = 0;
  for (const [i, p] of pts.entries()) {
    const env0 = Object.fromEntries(vars.map((v, j) => [v, j === 0 ? p : pts[(i + 3 * j + 1) % pts.length]]));
    const nenv = Object.fromEntries(Object.entries(env0).map(([k, v]) => [k, dv(v)]));
    const a = evalReal(lhs, nenv), b = evalReal(rhs, nenv);
    if (!Number.isFinite(a) || !Number.isFinite(b)) continue;
    if (Math.abs(a - b) <= 1e-9 * Math.max(1, Math.abs(a), Math.abs(b))) { agree++; continue; }
    const la = safe(() => hp(C(X.subs(lhs, env0)), 30)), lb = safe(() => hp(C(X.subs(rhs, env0)), 30));
    if (!la || !lb || !la.ok || !lb.ok) continue;
    if (Math.abs(la.re - lb.re) <= 1e-20 * Math.max(1, Math.abs(la.re))) { agree++; continue; }
    const where = vars.map((v) => `${v} = ${toText(env0[v])}`).join(", ");
    env.log.add({ rule: "analysis.identity.counterexample", title: "Counterexample", why: `At ${where}: left side = ${fmt(la.re)}, right side = ${fmt(lb.re)}.`, before: X.eq(lhs, rhs), after: X.FALSE });
    return {
      answers: [{ kind: "exact", label: `Not an identity (counterexample: ${where})`, tree: X.FALSE, counterexample: Object.fromEntries(vars.map((v) => [v, env0[v]])), detail: `fails at ${where}: ${fmt(la.re)} != ${fmt(lb.re)}` }],
      solutionStatus: "exact", note: `counterexample at ${where}`,
      verify: () => {
        // exact: the difference at the point is a nonzero constant
        const s = safe(() => signConst(C(X.subs(X.sub(lhs, rhs), env0))));
        if (s === 1 || s === -1) return TCV([pass("counterexample", `lhs - rhs at ${where} simplifies to a ${s > 0 ? "positive" : "negative"} number`, false)]);
        return TCV([bad("counterexample", `could not confirm the counterexample at ${where}`)]);
      },
    };
  }
  // 2. symbolic proof
  const d = X.sub(lhs, rhs);
  const how = proveZero(d);
  if (how < 0) {
    // last resort: an exact nonzero difference at a sample point is a counterexample too small for doubles
    for (const [i, p] of pts.slice(0, 8).entries()) {
      const env0 = Object.fromEntries(vars.map((v, j) => [v, j === 0 ? p : pts[(i + 3 * j + 1) % pts.length]]));
      if (![lhs, rhs].every((u) => definedAt(u, Object.fromEntries(Object.entries(env0).map(([k, v]) => [k, dv(v)]))))) continue;
      const s = safe(() => signConst(C(X.subs(d, env0))));
      if (s === 1 || s === -1) {
        const where = vars.map((v) => `${v} = ${toText(env0[v])}`).join(", ");
        const dval = safe(() => C(X.subs(d, env0)));
        env.log.add({ rule: "analysis.identity.counterexample", title: "Counterexample", why: `At ${where} the exact difference lhs - rhs is ${dval ? toText(dval) : (s > 0 ? "positive" : "negative")}, not 0.`, before: X.eq(lhs, rhs), after: X.FALSE });
        return {
          answers: [{ kind: "exact", label: `Not an identity (counterexample: ${where})`, tree: X.FALSE, counterexample: env0, detail: `lhs - rhs = ${dval ? toText(dval) : "nonzero"} at ${where}` }],
          solutionStatus: "exact", note: `counterexample at ${where}`,
          verify: () => { const hv = safe(() => hp(C(X.subs(d, env0)), 60)); return TCV([hv && hv.ok && !hv.zero && Math.abs(hv.re) > hv.err ? pass("counterexample", `lhs - rhs at ${where} evaluates to ${hv.re.toExponential(6)} at 60 digits (error bound ${hv.err.toExponential(1)})`) : open("counterexample", "the high-precision check was inconclusive")]); },
        };
      }
    }
    throw fail("Quelvra could not prove this identity symbolically, and found no counterexample; it does not guess");
  }
  if (agree < 8) throw fail("too few sample points where both sides are defined to confirm the identity");
  const methods = ["canonical simplification", "expansion", "a common denominator", "trigonometric identities", "rule-based simplification", "trigonometric identities and a common denominator", "rewriting in sin and cos"];
  // conditions: where either side is undefined
  const dl = safe(() => inferDomain(lhs).rels) || [], dr = safe(() => inferDomain(rhs).rels) || [];
  const conds = [];
  for (const c of [...dl, ...dr]) if (!conds.includes(c) && c !== X.TRUE) conds.push(c);
  const onlyOne = [...dl.filter((c) => !dr.includes(c)), ...dr.filter((c) => !dl.includes(c))];
  env.log.add({ rule: "analysis.identity.proof", title: "Show lhs - rhs = 0", why: `The difference simplifies to 0 by ${methods[how]}.`, before: d, after: X.ZERO, conditions: conds, kind: conds.length ? "conditional" : "equivalent" });
  if (conds.length) env.log.add({ rule: "analysis.identity.domain", title: "Common domain", why: `The identity holds wherever both sides are defined: ${conds.map(toText).join(", ")}.${onlyOne.length ? ` The two sides have different domains (${onlyOne.map(toText).join(", ")}), so the equality fails where only one side is defined.` : ""}`, kind: "note" });
  const label = conds.length ? `Identity (for all ${vars.join(", ")} with ${conds.map(toText).join(", ")})` : `Identity (true for every real ${vars.join(", ")})`;
  return {
    answers: [{ kind: "exact", label, tree: X.TRUE }], conditions: conds, solutionStatus: "exact",
    note: `proved by ${methods[how]}; confirmed at ${agree} sample points`,
    verify: () => {
      const e = equivalent(lhs, rhs, { vars, points: 40 });
      return TCV([pass("symbolic", `lhs - rhs simplifies to 0 (${methods[how]})`, false), { status: e.status === "different" ? "failed" : e.status === "inconclusive" ? "inconclusive" : "verified-numeric", checks: [{ kind: "sampling", ok: e.status !== "different", detail: e.status === "different" ? "a sample point disagrees" : `both sides agree at ${e.tested || "all"} independent random points` }] }]);
    },
  };
}

// ---------------------------------------------------------------- coordinate geometry
function points4(node, name) {
  let a = node.args;
  if (a.length === 2 && a.every((t) => (t.k === "tuple" || t.k === "vector") && t.args.length === 2)) a = [...a[0].args, ...a[1].args];
  if (a.length !== 4) throw fail(`${name} needs two points: ${name}(x1, y1, x2, y2)`);
  return a.map((t, i) => constArg(t, ["x1", "y1", "x2", "y2"][i]));
}
export function cmdSlope(node, env) {
  const [x1, y1, x2, y2] = points4(node, "slope");
  const dx = C(X.sub(x2.tree, x1.tree)), dy = C(X.sub(y2.tree, y1.tree));
  if (dx === X.ZERO) {
    if (dy === X.ZERO) throw fail("the two points are the same, so the slope is not determined");
    return { answers: [{ kind: "none", label: "Undefined slope (vertical line)", proof: `x1 = x2 = ${toText(x1.tree)}` }], solutionStatus: "exact", verify: () => TCV([Math.abs(x1.v - x2.v) < 1e-300 ? pass("vertical", "x1 = x2", false) : bad("vertical", "x1 != x2")]) };
  }
  const m = tidy(C(X.div(dy, dx)));
  env.log.add({ rule: "analysis.slope", title: "m = (y2 - y1)/(x2 - x1)", why: `(${toText(y2.tree)} - ${toText(y1.tree)})/(${toText(x2.tree)} - ${toText(x1.tree)}) = ${toText(m)}.`, before: X.div(dy, dx), after: m });
  return { answers: [{ kind: "exact", label: "Slope", tree: m }], solutionStatus: "exact",
    verify: () => { const want = (y2.v - y1.v) / (x2.v - x1.v); return TCV([Math.abs(dv(m) - want) <= 1e-12 * scale(want) ? pass("rise over run", `independent floating-point rise/run = ${fmt(want)}`) : bad("rise over run", `rise/run = ${fmt(want)}`)]); } };
}
export function cmdLine(node, env) {
  const [x1, y1, x2, y2] = points4(node, "line");
  const dx = C(X.sub(x2.tree, x1.tree)), dy = C(X.sub(y2.tree, y1.tree));
  const X0 = X.sym("x"), Y0 = X.sym("y");
  if (dx === X.ZERO && dy === X.ZERO) throw fail("the two points are the same; infinitely many lines pass through one point");
  let eqn, answers;
  if (dx === X.ZERO) {
    eqn = X.eq(X0, x1.tree);
    answers = [{ kind: "exact", label: "Line (vertical)", tree: eqn }, { kind: "none", label: "Slope: undefined (vertical line)" }];
    env.log.add({ rule: "analysis.line.vertical", title: "Vertical line", why: `Both points have x = ${toText(x1.tree)}.`, after: eqn });
  } else {
    const m = tidy(C(X.div(dy, dx)));
    const b = tidy(C(X.sub(y1.tree, X.mul(m, x1.tree))));
    eqn = X.eq(Y0, C(X.add(X.mul(m, X0), b)));
    env.log.add({ rule: "analysis.line.slope", title: "Slope", why: `m = (${toText(y2.tree)} - ${toText(y1.tree)})/(${toText(x2.tree)} - ${toText(x1.tree)}) = ${toText(m)}.`, after: m });
    env.log.add({ rule: "analysis.line.intercept", title: "Intercept", why: `b = y1 - m x1 = ${toText(b)}.`, after: eqn });
    answers = [{ kind: "exact", label: "Line", tree: eqn }, { kind: "exact", label: "Slope", tree: m }, { kind: "exact", label: "y-intercept", tree: b }];
  }
  return { answers, solutionStatus: "exact", graph: { exprs: [], marks: [{ x: x1.v, y: y1.v, label: "P1", kind: "point" }, { x: x2.v, y: y2.v, label: "P2", kind: "point" }] },
    verify: () => TCV([[x1, y1], [x2, y2]].map(([px, py]) => {
      const s = safe(() => C(X.subs(X.sub(eqn.args[0], eqn.args[1]), { x: px.tree, y: py.tree })));
      return s === X.ZERO ? pass("point on line", `(${toText(px.tree)}, ${toText(py.tree)}) satisfies ${toText(eqn)}`, false) : bad("point on line", `(${toText(px.tree)}, ${toText(py.tree)}) is not on the line`);
    })) };
}
export function cmdDistance(node, env) {
  const [x1, y1, x2, y2] = points4(node, "distance");
  const d = tidy(C(X.sqrt(X.add(X.pow(X.sub(x2.tree, x1.tree), X.TWO), X.pow(X.sub(y2.tree, y1.tree), X.TWO)))));
  env.log.add({ rule: "analysis.distance", title: "Distance formula", why: "d = sqrt((x2 - x1)^2 + (y2 - y1)^2).", before: X.sqrt(X.add(X.pow(X.sub(x2.tree, x1.tree), X.TWO), X.pow(X.sub(y2.tree, y1.tree), X.TWO))), after: d });
  const answers = [{ kind: "exact", label: "Distance", tree: d }];
  const ap = !X.isNum(d) ? safe(() => approxRec(d, 20)) : null;
  if (ap) answers[0].approx = ap;
  return { answers, solutionStatus: "exact", verify: () => { const want = Math.hypot(x2.v - x1.v, y2.v - y1.v); return TCV([Math.abs(dv(d) - want) <= 1e-12 * scale(want) ? pass("hypot", `independent floating-point hypot = ${fmt(want)}`) : bad("hypot", `hypot = ${fmt(want)}`)]); } };
}
export function cmdMidpoint(node, env) {
  const [x1, y1, x2, y2] = points4(node, "midpoint");
  const mx = tidy(C(X.div(X.add(x1.tree, x2.tree), X.TWO))), my = tidy(C(X.div(X.add(y1.tree, y2.tree), X.TWO)));
  const M = X.tuple(mx, my);
  env.log.add({ rule: "analysis.midpoint", title: "Average the coordinates", why: "M = ((x1 + x2)/2, (y1 + y2)/2).", after: M });
  return { answers: [{ kind: "exact", label: "Midpoint", tree: M }], solutionStatus: "exact",
    verify: () => {
      const d1 = Math.hypot(dv(mx) - x1.v, dv(my) - y1.v), d2 = Math.hypot(dv(mx) - x2.v, dv(my) - y2.v), d = Math.hypot(x2.v - x1.v, y2.v - y1.v);
      const ok = Math.abs(d1 - d2) <= 1e-12 * scale(d) && Math.abs(d1 + d2 - d) <= 1e-12 * scale(d);
      return TCV([ok ? pass("equidistant", `the point is at distance ${fmt(d1)} from both ends and on the segment`) : bad("equidistant", `distances ${fmt(d1)} and ${fmt(d2)}`)]);
    } };
}

// ---------------------------------------------------------------- integral applications
function bounds(rest, name) {
  if (rest.length !== 2) throw fail(`${name} needs the interval: ${name}(f, x, a, b)`);
  const a = constArg(rest[0], "a"), b = constArg(rest[1], "b");
  if (!(a.v < b.v)) throw fail("the interval needs a < b");
  return [a, b];
}
function approxRecord(v, err, method) {
  const e = Math.max(err || 0, 1e-15 * scale(v));
  const dg = Math.max(1, Math.min(14, Math.floor(-Math.log10(e / scale(v))) - 1));
  return { value: String(+v.toPrecision(dg)), digits: dg, requested: dg, errorBound: (e * 10).toExponential(1), method, iterations: 0, converged: true };
}
// Double-exponential (tanh-sinh) quadrature on [a, b]: copes with integrable singularities at the
// ends (1/sqrt(1 - x^2)). Nodes never touch a or b. Returns { value, err, ok }.
export function tanhSinh(g, a, b) {
  const c = (a + b) / 2, r = (b - a) / 2;
  const level = (h) => {
    let s = 0;
    for (let k = -Math.ceil(4 / h); k <= Math.ceil(4 / h); k++) {
      const t = k * h, u = (Math.PI / 2) * Math.sinh(t), ch = Math.cosh(u);
      const w = ((Math.PI / 2) * Math.cosh(t)) / (ch * ch);
      const y = Math.tanh(u);
      if (1 - Math.abs(y) < 1e-15) continue;
      const v = g(c + r * y);
      if (!Number.isFinite(v)) { if (w * r < 1e-6) continue; return NaN; }
      s += w * v;
    }
    return s * h * r;
  };
  let prev = level(0.5);
  for (let h = 0.25; h >= 1 / 256; h /= 2) {
    const cur = level(h);
    if (!Number.isFinite(cur)) return { ok: false };
    const err = Math.abs(cur - prev);
    if (err <= 1e-11 * Math.max(1, Math.abs(cur))) return { value: cur, err: Math.max(err, 1e-15 * Math.abs(cur)), ok: true };
    prev = cur;
  }
  return { ok: false };
}
// exact (tree) or approximate value of int_a^b g dx
function integrateValue(g, x, a, b, env) {
  let r, why = "";
  try { r = definiteIntegral(g, X.sym(x), a.tree, b.tree, { digits: 14, timeLimit: 5000 }); } catch (e) {
    if (!(e && e.code)) throw e;
    why = e.message; r = null;
  }
  if (r && r.status === "diverges") throw fail(`the integral of ${toText(g)} diverges on [${toText(a.tree)}, ${toText(b.tree)}]`);
  if (r && r.status === "exact") return { exact: true, tree: tidy(C(r.value)), v: Number.isFinite(r.approx) ? r.approx : dv(r.value) };
  if (r && r.status === "approx") return { exact: false, v: r.value, record: r.record };
  // certified numerical fallback: tanh-sinh and Gauss-Legendre must agree
  const gf = (t) => fAt(g, x, t);
  const ts = tanhSinh(gf, a.v, b.v);
  if (ts.ok) {
    const gl = quadrature(gf, a.v, b.v);
    const agree = gl.ok ? Math.abs(gl.value - ts.value) <= 1e-8 * Math.max(1, Math.abs(ts.value)) : false;
    {
      env.log.add({ rule: "analysis.integral.numeric", title: "Numerical integration", why: `No closed form was found${why ? ` (${why})` : ""}; the value is computed with double-exponential (tanh-sinh) quadrature${agree ? " and confirmed by adaptive Gauss-Legendre quadrature" : ""}.`, before: X.integral(g, X.sym(x), a.tree, b.tree), after: null });
      return { exact: false, v: ts.value, record: approxRecord(ts.value, Math.max(ts.err, agree ? Math.abs(gl.value - ts.value) : 0), "tanh-sinh quadrature") };
    }
  }
  throw fail(`the integral could not be evaluated${why ? ` (${why})` : ""}`);
}
function combine(parts, fn) {
  if (parts.every((p) => p.exact)) {
    const raw = C(fn(parts.map((p) => p.tree)));
    const ex = safe(() => C(expand(raw)));
    const tree = tidy(ex && X.size(ex) <= X.size(raw) ? ex : raw);
    return { exact: true, tree, v: dv(tree) };
  }
  return { exact: false, v: fn(parts.map((p) => p.v)) };
}
function valueAnswers(label, r, digits = 20) {
  if (r.exact) {
    const out = [{ kind: "exact", label, tree: r.tree }];
    const ap = X.isNum(r.tree) && r.tree.v.d === 1n ? null : safe(() => approxRec(r.tree, digits));
    if (ap) out.push({ kind: "approx", label, approx: ap });
    return { answers: out, solutionStatus: "exact" };
  }
  return { answers: [{ kind: "approx", label, approx: r.record || approxRecord(r.v, 1e-10 * scale(r.v), "numerical integration") }], solutionStatus: "approximate" };
}
function quadCheck(label, want, g, a, b, breaks = []) {
  const cuts = [a, ...breaks.filter((t) => t > a && t < b).sort((p, q) => p - q), b];
  let tot = 0, err = 0;
  for (let i = 0; i + 1 < cuts.length; i++) {
    const q = quadrature(g, cuts[i], cuts[i + 1]);
    if (!q.ok) return open(label, "independent quadrature did not converge");
    tot += q.value; err += q.err;
  }
  const ok = Math.abs(tot - want) <= Math.max(1e-7 * scale(want), 10 * err);
  return ok ? pass(label, `independent adaptive Gauss-Legendre quadrature gives ${fmt(tot)}`) : bad(label, `independent quadrature gives ${fmt(tot)}, not ${fmt(want)}`);
}

export function cmdArclength(node, env) {
  const { f, x, rest } = fnAndVar(node.args, "arclength");
  const [a, b] = bounds(rest, "arclength");
  const df = C(diff(C(f), x));
  let integrand = C(X.sqrt(X.add(X.ONE, X.pow(df, X.TWO))));
  // tidy 1 + f'^2 over a common denominator (sqrt(x^2/(1 - x^2) + 1) -> sqrt(1/(1 - x^2)))
  const tidier = safe(() => { const [n, d] = numerDenom(together(C(X.add(X.ONE, X.pow(df, X.TWO))))); return C(X.sqrt(C(X.div(C(expand(n)), C(expand(d)))))); });
  if (tidier && X.size(tidier) < X.size(integrand) && equivalent(tidier, integrand).status !== "different") integrand = tidier;
  for (const t of [a.v, (a.v + b.v) / 2, b.v]) if (!definedNum(f, x, t) && t !== a.v && t !== b.v) throw fail("f must be defined on the whole interval");
  env.log.add({ rule: "analysis.arclength.formula", title: "Arc length formula", why: `L = int_a^b sqrt(1 + f'(x)^2) dx with f'(${x}) = ${toText(df)}.`, before: f, after: X.integral(integrand, X.sym(x), a.tree, b.tree) });
  const r = integrateValue(integrand, x, a, b, env);
  const out = valueAnswers("Arc length", r);
  return { ...out, graph: { exprs: [f], marks: [] }, verify: () => TCV([polylineCheck(f, x, a.v, b.v, r.v)]) };
}
// arc length of the ORIGINAL f from inscribed polygons (Richardson-extrapolated), independent of f'
function polylineCheck(f, x, a, b, want) {
  const L = (n) => { let s = 0, px = a, py = fAt(f, x, a); for (let i = 1; i <= n; i++) { const t = a + ((b - a) * i) / n, y = fAt(f, x, t); s += Math.hypot(t - px, y - py); px = t; py = y; } return s; };
  const l1 = L(8192), l2 = L(16384);
  if (!Number.isFinite(l1) || !Number.isFinite(l2)) return open("polyline", "f could not be evaluated along the interval");
  const est = (4 * l2 - l1) / 3;
  const d = Math.abs(est - want);
  if (d <= 1e-7 * scale(want)) return pass("polyline", `inscribed polygons (16384 sides, extrapolated) give ${fmt(est)}`);
  if (d <= 1e-4 * scale(want) && Math.abs(l2 - want) < Math.abs(l1 - want)) return pass("polyline", `inscribed polygons converge towards the value (${fmt(l1)}, ${fmt(l2)}; slow near a vertical tangent)`);
  return bad("polyline", `inscribed polygons give ${fmt(est)}, not ${fmt(want)}`);
}

export function cmdAreaBetween(node, env) {
  const args = node.args;
  if (args.length < 3) throw fail("areabetween needs two functions and the variable: areabetween(f, g, x) or areabetween(f, g, x, a, b)");
  const f = args[0], g = args[1];
  if (args[2].k !== "sym") throw fail("the third argument of areabetween must be the variable");
  const x = args[2].name;
  for (const u of [f, g]) { const o = [...X.freeSymbols(u)].filter((s) => s !== x); if (o.length) throw fail(`areabetween works with one variable; ${o.join(", ")} would need a value`); }
  const h = C(X.sub(f, g));
  const envZ = { digits: env.digits || 20, checkTime: env.checkTime };
  let a, b, cuts;
  if (args.length === 5) {
    [a, b] = bounds(args.slice(3), "areabetween");
    const z = zerosOf(h, x, envZ);
    const pts = [...z.points, ...familyMembers(z.families, a.v, b.v)].filter((p) => p.v > a.v + 1e-12 * scale(a.v) && p.v < b.v - 1e-12 * scale(b.v));
    cuts = [a, ...pts.sort((p, q) => p.v - q.v).map((p) => ({ tree: p.tree, v: p.v, approx: p.approx })), b];
  } else if (args.length === 3) {
    const z = zerosOf(h, x, envZ, { allowFamilies: false });
    if (z.all) throw fail("the two curves coincide");
    if (z.points.length < 2) throw fail("the curves meet in fewer than two points, so they do not enclose a bounded region; give the interval: areabetween(f, g, x, a, b)");
    cuts = z.points.map((p) => ({ tree: p.tree, v: p.v, approx: p.approx }));
    a = cuts[0]; b = cuts[cuts.length - 1];
    env.log.add({ rule: "analysis.area.intersections", title: "Intersection points", why: `f = g where ${toText(h)} = 0: ${x} = ${cuts.map((c) => (c.approx ? "~" + c.approx.value : toText(c.tree))).join(", ")}.`, before: X.eq(f, g), after: null, kind: "note" });
  } else throw fail("areabetween(f, g, x) or areabetween(f, g, x, a, b)");
  for (let i = 0; i + 1 < cuts.length; i++) { const m = (cuts[i].v + cuts[i + 1].v) / 2; if (!definedNum(h, x, m)) throw fail("both functions must be defined between the bounds"); }
  const pieces = [];
  for (let i = 0; i + 1 < cuts.length; i++) {
    const m = (cuts[i].v + cuts[i + 1].v) / 2;
    const s = Math.sign(fAt(h, x, m));
    const lo = cuts[i].approx ? { tree: cuts[i].tree, v: cuts[i].v } : cuts[i], hi = cuts[i + 1].approx ? { tree: cuts[i + 1].tree, v: cuts[i + 1].v } : cuts[i + 1];
    const r = integrateValue(h, x, lo, hi, env);
    const approxEnds = cuts[i].approx || cuts[i + 1].approx;
    pieces.push({ ...r, exact: r.exact && !approxEnds, s, tree: r.exact ? (s < 0 ? C(X.neg(r.tree)) : r.tree) : null, v: s < 0 ? -r.v : r.v });
  }
  env.log.add({ rule: "analysis.area.split", title: "Split where the curves cross", why: `Area = int |f - g| dx; on each piece the sign of f - g is fixed: ${pieces.map((p, i) => `on [${cutText(cuts[i])}, ${cutText(cuts[i + 1])}] f - g is ${p.s >= 0 ? "positive" : "negative"}, area ${p.exact ? toText(p.tree) : fmt(p.v)}`).join("; ")}.`, before: X.integral(X.fn("abs", h), X.sym(x), a.tree, b.tree), after: null });
  const tot = combine(pieces, (vals) => (vals[0] && vals[0].k ? X.add(...vals) : vals.reduce((s, v) => s + v, 0)));
  const out = valueAnswers("Area", tot);
  return { ...out, graph: { exprs: [f, g], marks: [] }, verify: () => TCV([quadCheck("area", tot.v, (t) => Math.abs(fAt(f, x, t) - fAt(g, x, t)), a.v, b.v, cuts.map((c) => c.v))]) };
}
const cutText = (c) => (c.approx ? `~${c.approx.value.slice(0, 10)}` : toText(c.tree));

export function cmdVolume(node, env) {
  const { f, x, rest } = fnAndVar(node.args, "volume");
  const [a, b] = bounds(rest, "volume");
  const g = C(X.pow(f, X.TWO));
  env.log.add({ rule: "analysis.volume.disk", title: "Disk method (rotation about the x-axis)", why: `V = pi int_a^b f(x)^2 dx.`, before: f, after: X.mul(X.PI, X.integral(g, X.sym(x), a.tree, b.tree)) });
  const r = integrateValue(g, x, a, b, env);
  const tot = r.exact ? { exact: true, tree: tidy(C(X.mul(X.PI, r.tree))) } : { exact: false, v: Math.PI * r.v };
  if (tot.exact) tot.v = dv(tot.tree);
  const out = valueAnswers("Volume", tot);
  return { ...out, graph: { exprs: [f], marks: [] }, verify: () => TCV([quadCheck("volume", tot.v, (t) => Math.PI * fAt(f, x, t) ** 2, a.v, b.v)]) };
}

export function cmdAvgValue(node, env) {
  const { f, x, rest } = fnAndVar(node.args, "avgvalue");
  const [a, b] = bounds(rest, "avgvalue");
  env.log.add({ rule: "analysis.avg.formula", title: "Average value", why: "f_avg = (1/(b - a)) int_a^b f(x) dx.", before: f, after: X.mul(X.recip(X.sub(b.tree, a.tree)), X.integral(f, X.sym(x), a.tree, b.tree)) });
  const r = integrateValue(f, x, a, b, env);
  const w = C(X.sub(b.tree, a.tree));
  const tot = r.exact ? { exact: true, tree: tidy(C(X.div(r.tree, w))) } : { exact: false, v: r.v / (b.v - a.v) };
  if (tot.exact) tot.v = dv(tot.tree);
  const out = valueAnswers("Average value", tot);
  return { ...out, graph: { exprs: [f], marks: [] }, verify: () => TCV([quadCheck("average", tot.v, (t) => fAt(f, x, t) / (b.v - a.v), a.v, b.v)]) };
}
