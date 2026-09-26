// Quelvra solvers: the univariate equation engine.
//
// solveCore(expr, S) finds every x with expr = 0. It returns a SUPERSET description
//   { exact: [{tree, multiplicity?}], approx: [{value, approx, tree?}], general: [family],
//     regions: [relation], all, complete, methods: [..], notes: [..] }
// in which every transformation used was an equivalence or an implication, so the true solutions
// are among the candidates whenever `complete` is true. The caller checks every candidate against
// the ORIGINAL equation (solve/equation.js) and rejects extraneous ones with a reason.
//
// Methods, in order: constant / identity, polynomial over Q, constant-coefficient linear or
// quadratic, clearing denominators, products, isolation (inverting one occurrence), absolute
// value case split, radical elimination (isolate + raise to a power, or a resultant), trigonometric
// (trig.js), hyperbolic -> exponential rewrite, kernel substitution (b^x, ln x, ...), exponential
// terms compared by logarithms, combining logarithms, Lambert W forms (lambert.js), and finally
// certified numerics (numeric.js) when nothing exact applies.

import * as X from "../expr.js";
import * as Q from "../num.js";
import * as P from "../poly.js";
import { toText } from "../print.js";
import { C, EX, TOG, numDen, tidy, safe, signConst, isZeroExact, hasFn, num, fail, findAll, cmpConst, denominators } from "./util.js";
import { coeffTrees, isRationalPoly, toUPoly, solveUPoly } from "./poly.js";
import { solveTrig, trigInvert, isTrigName, linearIn } from "./trig.js";
import { solveLambert } from "./lambert.js";
import { solveNumeric } from "./numeric.js";

export const emptySol = () => ({ exact: [], approx: [], general: [], regions: [], all: false, complete: true, methods: [], notes: [] });
export function mergeSol(a, b) {
  return {
    exact: [...a.exact, ...b.exact], approx: [...a.approx, ...b.approx], general: [...a.general, ...b.general],
    regions: [...a.regions, ...b.regions], all: a.all || b.all, complete: a.complete && b.complete,
    methods: [...new Set([...a.methods, ...b.methods])], notes: [...a.notes, ...b.notes], window: a.window || b.window,
  };
}
const HYP = new Set(["sinh", "cosh", "tanh", "coth", "sech", "csch"]);
const MAX_DEPTH = 9;

export function depends(u, x) { return !X.freeOf(u, x); }
function xTerms(expr, x) {
  const terms = expr.k === "add" ? expr.args : [expr];
  return [terms.filter((t) => depends(t, x)), terms.filter((t) => !depends(t, x))];
}
let FRESH = 0;
export function fresh(base, avoid) { let n; do { n = `${base}${++FRESH}`; } while (avoid && X.hasSym(avoid, n)); return n; }

// ---------------------------------------------------------------- entry
export function solveCore(expr, S) {
  S.checkTime && S.checkTime();
  const depth = S.depth || 0;
  if (depth > MAX_DEPTH) throw fail("the equation needs too many nested transformations");
  const x = S.x;
  const sub = (e, extra = {}) => solveCore(e, { ...S, depth: depth + 1, ...extra });
  let e = C(expr, S.domain);
  if (e === X.UNDEF) return { ...emptySol(), notes: ["the equation is undefined everywhere"] };
  // 0. constant
  if (!depends(e, x)) {
    const s = signConst(e, S.domain);
    if (s === 0 || e === X.ZERO) return { ...emptySol(), all: true, methods: ["identity"] };
    if (s === 1 || s === -1 || (X.isNum(e))) return { ...emptySol(), methods: ["contradiction"], notes: [`the equation reduces to ${toText(e)} = 0, which is false`] };
    if (isZeroExact(e, S.domain)) return { ...emptySol(), all: true, methods: ["identity"] };
    throw fail("could not decide whether a constant is zero");
  }
  // 1. polynomial with rational coefficients
  const cs = coeffTrees(e, x);
  if (cs && isRationalPoly(cs)) {
    const r = solveUPoly(toUPoly(cs), x, S);
    if (r.identity) {
      S.log.add({ rule: "solve.identity", title: "Both sides are the same polynomial", why: "After expanding, every coefficient is 0, so the equation holds for every value.", before: X.eq(e, X.ZERO), after: X.TRUE });
      return { ...emptySol(), all: true, methods: ["identity"] };
    }
    const out = emptySol();
    out.methods.push(cs.length === 2 ? "linear" : cs.length === 3 ? "quadratic" : "polynomial");
    out.exact = r.exact.map((q) => ({ tree: q.tree, multiplicity: q.multiplicity, real: q.real, form: q.form }));
    out.approx = r.approx;
    out.sturm = r.realCount;
    out.polyDegree = r.degree;
    return out;
  }
  // 2. constant (non-rational) coefficients, degree 1 or 2
  if (cs && cs.every((c) => !X.freeSymbols(c).size) && cs.length <= 3) {
    const r = constCoeffPoly(cs, S);
    if (r) return r;
  }
  // 3. clear denominators
  const [n, d] = numDen(e, S.domain);
  if (depends(d, x) || (n !== e && denominators(e).some((q) => depends(q, x)))) {
    S.log.add({ rule: "solve.rational.clear", title: "Multiply by the common denominator", why: `Bring everything over the common denominator ${toText(d)} and keep only the numerator. Values that make an original denominator 0 are excluded afterwards.`, before: X.eq(e, X.ZERO), after: X.eq(n, X.ZERO), conditions: [X.rel("!=", d, X.ZERO)], kind: "conditional" });
    // If bringing to a common denominator cancelled a factor, multiply through by the original
    // denominators instead (the textbook route): the cancelled factor's zeros then appear as
    // candidates and are rejected by the check against the original equation.
    let target = n;
    const xd = [...new Set(denominators(e).filter((q) => depends(q, x)))];
    if (xd.length && xd.length <= 4) {
      const n2 = safe(() => {
        const terms = (e.k === "add" ? e.args : [e]).map((t) => {
          const [a, b] = numDen(X.mul(t, ...xd), S.domain);
          return depends(b, x) ? null : X.div(a, b);
        });
        return terms.some((t) => !t) ? null : C(EX(X.add(...terms), S.domain), S.domain);
      });
      const c2 = n2 && coeffTrees(n2, x), c1 = coeffTrees(n, x);
      if (c2 && isRationalPoly(c2) && c2.length > 1 && (!c1 || c2.length > c1.length) && (!c1 || isRationalPoly(c1))) {
        S.log.add({ rule: "solve.rational.multiply", title: "Multiply both sides by the denominators", why: `Multiplying by ${xd.map((q) => "(" + toText(q) + ")").join("")} gives ${toText(n2)} = 0; its roots are candidates that must not make a denominator 0.`, before: X.eq(e, X.ZERO), after: X.eq(n2, X.ZERO), kind: "conditional" });
        target = n2;
      }
    }
    const r = sub(target);
    r.methods.push("rational");
    return r;
  }
  // 4. product = 0
  const prod = productFactors(e, x);
  if (prod) {
    S.log.add({ rule: "solve.product.zero", title: "A product is zero when a factor is zero", why: `Solve each factor separately: ${prod.map((f) => toText(f) + " = 0").join(", ")}.`, before: X.eq(e, X.ZERO), after: X.or(...prod.map((f) => X.eq(f, X.ZERO))) });
    let out = emptySol();
    for (const f of prod) out = mergeSol(out, sub(f));
    out.methods.push("product");
    return out;
  }
  // 5. isolation (x occurs along a single chain)
  const iso = isolate(e, S, sub);
  if (iso) return iso;
  // 6. absolute values
  if (hasAbsIn(e, x)) { const r = solveAbs(e, S, sub); if (r) return r; }
  // 7. radicals
  if (hasRadicalIn(e, x)) { const r = solveRadical(e, S, sub); if (r) return r; }
  // 8. trigonometric
  if (hasTrigIn(e, x)) { const r = solveTrig(e, { ...S, solveCore: (u, extra) => sub(u, extra) }); if (r) return r; }
  // 9. hyperbolic -> exponential
  if (hasHypIn(e, x)) {
    const r2 = rewriteHyperbolic(e);
    if (r2 !== e) {
      S.log.add({ rule: "solve.hyperbolic.exp", title: "Write hyperbolic functions with exponentials", why: "sinh u = (e^u - e^-u)/2, cosh u = (e^u + e^-u)/2, tanh u = sinh u / cosh u.", before: X.eq(e, X.ZERO), after: X.eq(r2, X.ZERO) });
      const r = sub(r2);
      r.methods.push("hyperbolic");
      return r;
    }
  }
  // 9b. variable base and variable exponent: g^h = e^(h ln g) for g > 0
  const vp = findAll(e, (w) => w.k === "pow" && depends(w.args[0], x) && depends(w.args[1], x));
  if (vp.length) {
    let r2 = e;
    for (const w of vp) r2 = X.replace(r2, w, X.exp(X.mul(w.args[1], X.fn("ln", w.args[0]))));
    S.log.add({ rule: "solve.power.exp-log", title: "Write the power with e and ln", why: "For a positive base, g^h = e^(h ln g). A power with a variable base is taken for g > 0 (integer points with g < 0 are tested separately).", before: X.eq(e, X.ZERO), after: X.eq(r2, X.ZERO), conditions: vp.map((w) => X.rel(">", w.args[0], X.ZERO)), kind: "conditional" });
    const r = sub(C(r2, S.domain));
    // negative integers where the power is real (g an integer < 0 and h an integer)
    for (let n = -1; n >= -12; n--) {
      const t = num(n);
      const ok = safe(() => vp.every((w) => { const g = C(X.subs(w.args[0], { [x]: t })), h = C(X.subs(w.args[1], { [x]: t })); return X.isInt(g) && X.isInt(h); }) && isZeroExact(X.subs(e, { [x]: t }), S.domain));
      if (ok) r.exact.push({ tree: t, multiplicity: 1 });
    }
    r.notes.push("powers with a variable base were taken for a positive base; negative integers from -12 to -1 were also tested");
    r.methods.push("variable-power");
    return r;
  }
  // 10. logarithms of constant base -> ln; single kernel substitution
  const kern = kernelSubstitute(e, S, sub);
  if (kern) return kern;
  // 11. exponential terms compared by logarithms
  const el = expLogBothSides(e, S, sub);
  if (el) return el;
  // 12. combine logarithms
  const lc = combineLogs(e, S, sub);
  if (lc) return lc;
  // 13. Lambert W
  const lw = solveLambert(e, { ...S, solveCore: (u, extra) => sub(u, extra) });
  if (lw) return lw;
  // 14. certified numerics (only for the original unknown; approximations cannot be pushed through a substitution)
  if (S.allowNumeric && x === S.topVar) {
    const r = solveNumeric(e, S);
    if (r) return r;
  }
  throw fail(`no exact method applies to ${toText(e)} = 0`);
}

// ---------------------------------------------------------------- constant coefficients
function constCoeffPoly(cs, S) {
  const x = S.x, X0 = X.sym(x);
  const out = emptySol();
  if (cs.length === 2) {
    const [b, a] = cs;
    const sa = signConst(a, S.domain);
    if (!sa) return null;
    const r = tidy(X.neg(X.div(b, a)), S.domain);
    S.log.add({ rule: "solve.linear.divide", title: `Solve for ${x}`, why: `Divide by the coefficient ${toText(a)} (not 0).`, before: X.eq(X.add(X.mul(a, X0), b), X.ZERO), after: X.eq(X0, r) });
    out.exact.push({ tree: r, multiplicity: 1 });
    out.methods.push("linear");
    return out;
  }
  if (cs.length === 3) {
    const [c, b, a] = cs;
    if (!signConst(a, S.domain)) return null;
    const D = tidy(EX(X.sub(X.pow(b, X.TWO), X.mul(num(4), a, c))), S.domain);
    const sd = signConst(D, S.domain);
    if (sd === null) return null;
    S.log.add({ rule: "solve.quadratic.discriminant", title: "Compute the discriminant", why: `a = ${toText(a)}, b = ${toText(b)}, c = ${toText(c)}.`, before: null, after: X.eq(X.sym("D"), D) });
    out.methods.push("quadratic");
    if (sd < 0 && S.domain === "real") { out.notes.push("negative discriminant"); return out; }
    if (sd === 0) { out.exact.push({ tree: tidy(X.div(X.neg(b), X.mul(X.TWO, a)), S.domain), multiplicity: 2 }); return out; }
    const s = X.sqrt(D), den = X.mul(X.TWO, a);
    const r1 = tidy(X.div(X.sub(X.neg(b), s), den), S.domain), r2 = tidy(X.div(X.add(X.neg(b), s), den), S.domain);
    S.log.add({ rule: "solve.quadratic.formula", title: "Apply the quadratic formula", why: "x = (-b +- sqrt(D)) / (2a).", before: null, after: X.or(X.eq(X0, r1), X.eq(X0, r2)) });
    out.exact.push({ tree: r1, multiplicity: 1 }, { tree: r2, multiplicity: 1 });
    return out;
  }
  return null;
}

// ---------------------------------------------------------------- products
function productFactors(e, x) {
  if (e.k === "pow" && X.isInt(e.args[1]) && e.args[1].v.n > 1n && depends(e.args[0], x)) return [e.args[0]];
  if (e.k !== "mul") return null;
  const fs = [];
  for (const f of e.args) {
    if (!depends(f, x)) continue;
    if (f.k === "pow" && X.isNum(f.args[1]) && Q.isPos(f.args[1].v) && X.freeOf(f.args[1], x)) fs.push(f.args[0]);
    else fs.push(f);
  }
  return fs.length >= 2 ? fs : null;
}

// ---------------------------------------------------------------- isolation
// If x occurs in exactly one term, peel the outer operations off one at a time.
function isolable(u, x) {
  if (!depends(u, x)) return true;
  if (u.k === "sym") return true;
  const ds = u.args.filter((a) => depends(a, x));
  if (ds.length !== 1) return false;
  return isolable(ds[0], x);
}
export function isolate(e, S, sub) {
  const x = S.x, X0 = X.sym(x), dom = S.domain;
  const [xs, cs] = xTerms(e, x);
  if (xs.length !== 1) return null;
  if (xs[0] === X0) return null; // linear already handled
  if (!isolable(xs[0], x) && !peelable(xs[0], x)) return null;
  let steps = 0;
  const residual = [];
  let branches = [{ f: xs[0], c: C(X.neg(X.add(...cs)), dom) }];
  const done = emptySol();
  done.methods.push("isolation");
  for (let guard = 0; guard < 60 && branches.length; guard++) {
    S.checkTime && S.checkTime();
    const next = [];
    for (const { f, c } of branches) {
      if (f === X0) { done.exact.push({ tree: tidy(c, dom), multiplicity: 1 }); continue; }
      const r = invertStep(f, c, S);
      if (r === null) {
        if (steps === 0 || !sub) return null; // cannot invert: let another method try
        residual.push(C(X.sub(f, c), dom));
        continue;
      }
      steps++;
      if (r.general) { done.general.push(...r.general); continue; }
      if (r.note) done.notes.push(r.note);
      if (r.all) { done.regions.push(r.all); continue; }
      next.push(...r.branches);
    }
    branches = next;
  }
  if (branches.length) return null;
  let out = done;
  for (const r of residual) out = mergeSol(out, sub(r));
  return out;
}
// the outermost operation has a single x-dependent argument (so at least one inversion step applies)
function peelable(u, x) {
  if (u.k === "sym" || !depends(u, x)) return false;
  return u.args.filter((a) => depends(a, x)).length === 1;
}
function step(S, rule, title, why, before, after, extra = {}) { S.log.add({ rule, title, why, before, after, ...extra }); }
function sgn(c, S) { return signConst(c, S.domain); }
// One inversion step for f(...) = c. Returns { branches: [{f, c}] } | { general } | null.
function invertStep(f, c, S) {
  const x = S.x, dom = S.domain;
  const E0 = X.eq(f, c);
  const none = (why) => { step(S, "solve.isolate.none", "No solution on this branch", why, E0, X.FALSE); return { branches: [] }; };
  if (f.k === "add") {
    const [xs, cs] = xTerms(f, x);
    if (xs.length !== 1) return null;
    const nc = C(X.sub(c, X.add(...cs)), dom);
    step(S, "solve.isolate.subtract", "Move the constant terms", "Subtract the same quantity from both sides.", E0, X.eq(xs[0], nc));
    return { branches: [{ f: xs[0], c: nc }] };
  }
  if (f.k === "mul") {
    const xs = f.args.filter((a) => depends(a, x)), ks = f.args.filter((a) => !depends(a, x));
    if (xs.length !== 1) return null;
    const k = C(X.mul(...ks), dom);
    const s = sgn(k, S);
    if (!s) return null;
    const nc = tidy(X.div(c, k), dom);
    step(S, "solve.isolate.divide", "Divide both sides", `Divide by ${toText(k)} (not 0).`, E0, X.eq(xs[0], nc));
    return { branches: [{ f: xs[0], c: nc }] };
  }
  if (f.k === "pow") {
    const [b, ex] = f.args;
    const bx = depends(b, x), ex_ = depends(ex, x);
    if (bx && !ex_) return invertPower(b, ex, c, S, E0);
    if (!bx && ex_) {
      // b^A = c
      const sb = sgn(b, S);
      if (sb !== 1) return null;
      if (isZeroExact(X.sub(b, X.ONE), dom)) {
        const s0 = sgn(X.sub(c, X.ONE), S);
        if (s0 === 0) return { all: X.TRUE, branches: [] };
        return none("1 to any power is 1.");
      }
      const sc = sgn(c, S);
      if (sc === null) return null;
      if (sc <= 0) return none(`${toText(b)}^(...) is always positive, so it cannot equal ${toText(c)}.`);
      const nc = b === X.E ? tidy(X.fn("ln", c), dom) : tidy(X.div(X.fn("ln", c), X.fn("ln", b)), dom);
      step(S, "solve.isolate.log", "Take logarithms", b === X.E ? "e^A = c with c > 0 means A = ln c." : `${toText(b)}^A = c with c > 0 means A = ln c / ln ${toText(b)}.`, E0, X.eq(ex, nc));
      return { branches: [{ f: ex, c: nc }] };
    }
    return null;
  }
  if (f.k === "fn") {
    const name = f.name;
    if (name === "log" && f.args.length === 2) {
      const [b, a] = f.args;
      if (!depends(b, x)) {
        const nc = tidy(X.pow(b, c), dom);
        const sb = sgn(b, S);
        if (sb !== 1 || isZeroExact(X.sub(b, X.ONE), dom)) return null;
        step(S, "solve.isolate.exp", "Rewrite in exponential form", `log_b(A) = c means A = b^c (with A > 0).`, E0, X.eq(a, nc));
        return { branches: [{ f: a, c: nc }] };
      }
      if (!depends(a, x)) {
        // log_A(k) = c  <=>  ln k = c ln A  <=>  A = k^(1/c)   (A > 0, A != 1)
        const sc = sgn(c, S);
        if (sc === null) return null;
        if (sc === 0) {
          if (isZeroExact(X.sub(a, X.ONE), dom)) return { all: X.TRUE, branches: [] };
          return none(`log_A(${toText(a)}) = 0 would need ${toText(a)} = 1.`);
        }
        const nc = tidy(X.pow(a, X.div(X.ONE, c)), dom);
        step(S, "solve.isolate.base", "Solve for the base", `log_A(k) = c means A^c = k, so A = k^(1/c) (A > 0, A != 1).`, E0, X.eq(b, nc));
        return { branches: [{ f: b, c: nc }] };
      }
      return null;
    }
    if (f.args.length !== 1) return null;
    const A = f.args[0];
    const branch = (nc, rule, title, why) => { nc = tidy(nc, dom); step(S, rule, title, why, E0, X.eq(A, nc)); return { f: A, c: nc }; };
    switch (name) {
      case "ln": return { branches: [branch(X.pow(X.E, c), "solve.isolate.exp", "Exponentiate", "ln A = c means A = e^c.")] };
      case "exp": { const sc = sgn(c, S); if (sc === null) return null; if (sc <= 0) return none("e^A > 0."); return { branches: [branch(X.fn("ln", c), "solve.isolate.log", "Take ln", "e^A = c means A = ln c.")] }; }
      case "abs": {
        const sc = sgn(c, S);
        if (sc === null) return null;
        if (sc < 0) return none(`An absolute value is never negative, so |A| = ${toText(c)} is impossible.`);
        if (sc === 0) return { branches: [branch(X.ZERO, "solve.isolate.abs", "Absolute value zero", "|A| = 0 means A = 0.")] };
        step(S, "solve.isolate.abs", "Split the absolute value", `|A| = ${toText(c)} means A = ${toText(c)} or A = -${toText(c)}.`, E0, X.or(X.eq(A, c), X.eq(A, C(X.neg(c), dom))));
        return { branches: [{ f: A, c }, { f: A, c: C(X.neg(c), dom) }] };
      }
      case "sqrt": return invertPower(A, X.HALF, c, S, E0);
      case "cbrt": return invertPower(A, num(1, 3), c, S, E0);
      case "asin": case "acos": case "atan": {
        const [lo, hi, loOpen, hiOpen] = name === "asin" ? [X.mul(num(-1, 2), X.PI), X.mul(num(1, 2), X.PI), false, false] : name === "acos" ? [X.ZERO, X.PI, false, false] : [X.mul(num(-1, 2), X.PI), X.mul(num(1, 2), X.PI), true, true];
        const a = cmpConst(c, lo, dom), b = cmpConst(c, hi, dom);
        if (a === null || b === null) return null;
        if (a < 0 || b > 0 || (a === 0 && loOpen) || (b === 0 && hiOpen)) return none(`${name} only takes values in ${loOpen ? "(" : "["}${toText(C(lo))}, ${toText(C(hi))}${hiOpen ? ")" : "]"}.`);
        const inv = { asin: "sin", acos: "cos", atan: "tan" }[name];
        return { branches: [branch(X.fn(inv, c), "solve.isolate.inverse-trig", `Apply ${inv}`, `${name}(A) = c with c in the range of ${name} means A = ${inv}(c).`)] };
      }
      case "sinh": return { branches: [branch(X.fn("asinh", c), "solve.isolate.hyperbolic", "Apply asinh", "sinh is one-to-one: sinh A = c means A = asinh c = ln(c + sqrt(c^2 + 1)).")] };
      case "tanh": {
        const a = cmpConst(c, X.NEG_ONE, dom), b = cmpConst(c, X.ONE, dom);
        if (a === null || b === null) return null;
        if (a <= 0 || b >= 0) return none("tanh takes values strictly between -1 and 1.");
        return { branches: [branch(X.fn("atanh", c), "solve.isolate.hyperbolic", "Apply atanh", "tanh is one-to-one onto (-1, 1).")] };
      }
      case "cosh": {
        const a = cmpConst(c, X.ONE, dom);
        if (a === null) return null;
        if (a < 0) return none("cosh A >= 1 for every real A.");
        if (a === 0) return { branches: [branch(X.ZERO, "solve.isolate.hyperbolic", "cosh A = 1", "cosh A = 1 only at A = 0.")] };
        const r = tidy(X.fn("acosh", c), dom);
        step(S, "solve.isolate.hyperbolic", "Apply acosh (two signs)", "cosh is even: cosh A = c > 1 means A = acosh c or A = -acosh c.", E0, X.or(X.eq(A, r), X.eq(A, C(X.neg(r), dom))));
        return { branches: [{ f: A, c: r }, { f: A, c: C(X.neg(r), dom) }] };
      }
      case "asinh": return { branches: [branch(X.fn("sinh", c), "solve.isolate.hyperbolic", "Apply sinh", "asinh is one-to-one.")] };
      case "acosh": { const s = sgn(c, S); if (s === null) return null; if (s < 0) return none("acosh takes values >= 0."); return { branches: [branch(X.fn("cosh", c), "solve.isolate.hyperbolic", "Apply cosh", "acosh A = c >= 0 means A = cosh c.")] }; }
      case "atanh": return { branches: [branch(X.fn("tanh", c), "solve.isolate.hyperbolic", "Apply tanh", "atanh is one-to-one.")] };
      default:
        if (isTrigName(name)) {
          const lin = linearIn(A, x);
          if (!lin) return null;
          const fam = trigInvert(name, c, lin, S);
          if (!fam) return null;
          return { general: fam };
        }
        return null;
    }
  }
  return null;
}
// b^e = c with e constant.
function invertPower(b, e, c, S, E0) {
  const dom = S.domain;
  const none = (why) => { step(S, "solve.isolate.none", "No solution on this branch", why, E0, X.FALSE); return { branches: [] }; };
  if (!X.isNum(e)) {
    // irrational exponent: b > 0 required
    const sc = sgn(c, S);
    if (sc === null) return null;
    if (sc <= 0) return none("A positive base to a real power is positive.");
    const nc = tidy(X.pow(c, X.div(X.ONE, e)), dom);
    step(S, "solve.isolate.root", "Take the root", `A^${toText(e)} = c > 0 means A = c^(1/${toText(e)}).`, E0, X.eq(b, nc));
    return { branches: [{ f: b, c: nc }] };
  }
  const p = e.v.n, q = e.v.d;
  if (dom === "complex" && (q !== 1n || (p !== 1n && p !== -1n))) return null; // complex roots are handled by the polynomial solver
  const sc = sgn(c, S);
  if (sc === null) return null;
  // s = b^(1/q) (real); s^p = c
  const sBr = [];
  const ap = p < 0n ? -p : p;
  if (p < 0n && sc === 0) return none("A negative power is never 0.");
  if (ap % 2n === 1n) sBr.push(C(X.pow(c, X.num(Q.Q(1n, p))), dom));
  else {
    if (sc < 0) return none(`An even power is never negative, so it cannot equal ${toText(c)}.`);
    if (sc === 0) sBr.push(X.ZERO);
    else { const r = C(X.pow(c, X.num(Q.Q(1n, p))), dom); sBr.push(r, C(X.neg(r), dom)); }
  }
  const out = [];
  for (const s of sBr) {
    if (q % 2n === 0n && sgn(s, S) === -1) { step(S, "solve.isolate.even-root", "Rejected branch", `An even root is never negative, so ${toText(C(X.pow(b, X.num(Q.Q(1n, q)))))} = ${toText(s)} is impossible.`, null, null, { kind: "note" }); continue; }
    out.push({ f: b, c: tidy(X.pow(s, X.num(Q.Q(q))), dom) });
  }
  if (!out.length) return { branches: [] };
  step(S, q === 1n ? "solve.isolate.root" : "solve.isolate.power", q === 1n ? "Take the root" : "Raise both sides to a power", q === 1n ? (ap % 2n === 0n ? "An even power: both signs of the root." : "An odd power has exactly one real root.") : `A^(${Q.toString(e.v)}) = c; the ${q}th root is ${q % 2n === 0n ? "nonnegative" : "real"}, then raise to the power ${q}.`, E0, X.or(...out.map((o) => X.eq(b, o.c))));
  return { branches: out };
}

// ---------------------------------------------------------------- absolute values
function absNodes(u, x) { return findAll(u, (w) => w.k === "fn" && w.name === "abs" && depends(w, x)); }
function hasAbsIn(u, x) { return absNodes(u, x).length > 0; }
function solveAbs(e, S, sub) {
  const x = S.x, dom = S.domain;
  const nodes = absNodes(e, x).slice(0, 3);
  if (!nodes.length) return null;
  let out = emptySol();
  out.methods.push("absolute-value");
  const n = nodes.length;
  S.log.add({ rule: "solve.abs.cases", title: "Split into cases by the sign of each absolute value", why: nodes.map((a) => `|${toText(a.args[0])}| = ${toText(a.args[0])} when ${toText(a.args[0])} >= 0, and -(${toText(a.args[0])}) otherwise`).join("; ") + ". Every real x falls into at least one case.", before: X.eq(e, X.ZERO), after: null, kind: "note" });
  for (let mask = 0; mask < 1 << n; mask++) {
    let body = e;
    const conds = [];
    nodes.forEach((a, i) => {
      const g = a.args[0];
      const s = mask & (1 << i) ? -1 : 1;
      body = X.replace(body, a, s > 0 ? g : X.neg(g));
      conds.push(s > 0 ? X.rel(">=", g, X.ZERO) : X.rel("<=", g, X.ZERO));
    });
    body = C(body, dom);
    const cond = conds.length === 1 ? conds[0] : X.and(...conds);
    const r = S.log.group({ rule: "solve.abs.case", title: `Case ${toText(cond)}`, why: `Solve ${toText(body)} = 0 and keep the solutions with ${toText(cond)}.`, before: X.eq(body, X.ZERO), after: null }, () => safe(() => sub(body), "fail"));
    if (r === "fail" || r === null) throw fail("an absolute-value case could not be solved");
    if (r.all) { out.regions.push(cond); continue; }
    if (r.general.length) throw fail("periodic solutions inside an absolute value are not supported");
    // keep only candidates that satisfy the case condition (others belong to no case)
    const keep = (t) => conds.every((cd) => { const v = signConst(X.subs(X.sub(cd.args[0], cd.args[1]), { [x]: t }), dom); return v === null || (cd.op === ">=" ? v >= 0 : v <= 0); });
    out.exact.push(...r.exact.filter((q) => keep(q.tree)));
    out.approx.push(...r.approx);
    out.regions.push(...r.regions.map((g) => X.and(cond, g)));
    out.complete = out.complete && r.complete;
  }
  return out;
}

// ---------------------------------------------------------------- radicals
function isRadical(w, x) { return w.k === "pow" && X.isNum(w.args[1]) && w.args[1].v.d !== 1n && depends(w.args[0], x); }
function outerRadicals(u, x) {
  const out = [];
  const walk = (w) => {
    if (isRadical(w, x)) { out.push(w); return; }
    if (w.k === "fn" && (w.name === "sqrt" || w.name === "cbrt")) { out.push(w); return; }
    w.args.forEach(walk);
  };
  walk(u);
  return out;
}
function hasRadicalIn(u, x) { return outerRadicals(u, x).length > 0; }
function solveRadical(e, S, sub) {
  const x = S.x, dom = S.domain;
  const rads = outerRadicals(e, x).map((w) => (w.k === "fn" ? X.pow(w.args[0], w.name === "sqrt" ? X.HALF : num(1, 3)) : w));
  // radicand with the most complex structure first (outermost)
  const base = rads[0].args[0];
  const group = rads.filter((r) => r.args[0] === base);
  let qd = 1n;
  for (const r of group) qd = qd * r.args[1].v.d / Q.bgcd(qd, r.args[1].v.d);
  const tn = fresh("τ", e);
  const t = X.sym(tn);
  let g = e;
  for (const r of rads) if (r.args[0] === base) g = X.replace(g, r, X.pow(t, X.num(Q.mul(r.args[1].v, Q.Q(qd)))));
  // also the sqrt()/cbrt() function spellings
  g = X.mapTree(g, (w) => (w.k === "fn" && (w.name === "sqrt" || w.name === "cbrt") && w.args[0] === base ? X.pow(t, X.num(Q.Q(qd / (w.name === "sqrt" ? 2n : 3n)))) : w));
  g = C(g, dom);
  if (X.contains(g, base) && depends(g, x) && findAll(g, (w) => w.k === "pow" && w.args[0] === base && X.isNum(w.args[1]) && w.args[1].v.d !== 1n).length) throw fail("radical substitution failed");
  const [gn] = numDen(g, dom);
  const cs = coeffTrees(gn, tn);
  if (!cs) throw fail("radical equation is not polynomial in the radical");
  const q = Number(qd);
  // reduce modulo t^q = base
  const red = new Array(q).fill(X.ZERO);
  cs.forEach((c, i) => { red[i % q] = X.add(red[i % q], X.mul(c, X.pow(base, num(Math.floor(i / q))))); });
  const R = red.map((c) => C(c, dom));
  const radTree = C(X.pow(base, X.num(Q.Q(1n, qd))), dom);
  const top = R.map((c, i) => (c === X.ZERO ? -1 : i)).reduce((m, v) => Math.max(m, v), -1);
  let E;
  if (top <= 0) {
    E = R[0];
    S.log.add({ rule: "solve.radical.cancel", title: "The radical cancels", why: `Using (${toText(radTree)})^${q} = ${toText(base)}.`, before: X.eq(e, X.ZERO), after: X.eq(E, X.ZERO) });
  } else if (q === 2) {
    const [c0, c1] = R;
    const lhs = C(X.mul(c1, radTree), dom), rhs = C(X.neg(c0), dom);
    S.log.add({ rule: "solve.radical.isolate", title: "Isolate the square root", why: "Put the radical term alone on one side.", before: X.eq(e, X.ZERO), after: X.eq(lhs, rhs) });
    const L2 = EX(X.mul(X.pow(c1, X.TWO), base), dom), R2 = EX(X.pow(c0, X.TWO), dom);
    S.log.add({ rule: "solve.radical.square", title: "Square both sides", why: "Squaring can add extraneous solutions (where the two sides have opposite signs); every candidate is checked in the original equation.", before: X.eq(lhs, rhs), after: X.eq(L2, R2), kind: "conditional" });
    E = C(X.sub(L2, R2), dom);
  } else if (q === 3) {
    const [c0, c1, c2] = R;
    E = EX(X.add(X.pow(c0, num(3)), X.mul(X.pow(c1, num(3)), base), X.mul(X.pow(c2, num(3)), X.pow(base, X.TWO)), X.mul(num(-3), c0, c1, c2, base)), dom);
    S.log.add({ rule: "solve.radical.cube", title: c2 === X.ZERO ? "Isolate the cube root and cube both sides" : "Eliminate the cube root", why: c2 === X.ZERO ? "Cubing is reversible for real numbers, so no solutions are gained or lost." : "Multiply by the conjugate factors: a + b t + c t^2 = 0 with t^3 = u implies a^3 + b^3 u + c^3 u^2 - 3abc u = 0.", before: X.eq(e, X.ZERO), after: X.eq(E, X.ZERO) });
  } else {
    // general q: resultant with t^q - base when everything is polynomial over Q
    const vars = [x, tn];
    const A = safe(() => P.fromTree(X.add(...R.map((c, i) => X.mul(c, X.pow(t, num(i))))), vars));
    const B = safe(() => P.fromTree(X.sub(X.pow(t, num(q)), base), vars));
    if (!A || !B) throw fail("cannot eliminate this radical exactly");
    const res = P.mResultant(A, B, tn);
    E = P.toTree(res);
    S.log.add({ rule: "solve.radical.resultant", title: `Eliminate the ${q}th root with a resultant`, why: `Every solution of the original equation is a root of the resultant of a(t) and t^${q} - (${toText(base)}) with respect to t.`, before: X.eq(e, X.ZERO), after: X.eq(E, X.ZERO) });
  }
  const r = sub(E);
  r.methods.push("radical");
  return r;
}

// ---------------------------------------------------------------- trig / hyperbolic detection
function hasTrigIn(u, x) { return findAll(u, (w) => w.k === "fn" && isTrigName(w.name) && depends(w, x)).length > 0; }
function hasHypIn(u, x) { return findAll(u, (w) => w.k === "fn" && HYP.has(w.name) && depends(w, x)).length > 0; }
function rewriteHyperbolic(u) {
  return X.mapTree(u, (w) => {
    if (w.k !== "fn" || !HYP.has(w.name)) return w;
    const A = w.args[0];
    const ep = X.pow(X.E, A), em = X.pow(X.E, X.neg(A));
    const sh = X.div(X.sub(ep, em), X.TWO), ch = X.div(X.add(ep, em), X.TWO);
    switch (w.name) {
      case "sinh": return sh; case "cosh": return ch; case "tanh": return X.div(X.sub(ep, em), X.add(ep, em));
      case "coth": return X.div(X.add(ep, em), X.sub(ep, em)); case "sech": return X.div(X.TWO, X.add(ep, em)); case "csch": return X.div(X.TWO, X.sub(ep, em));
      default: return w;
    }
  });
}

// ---------------------------------------------------------------- kernel substitution
// Rewrite log(b, u) with constant b as ln(u)/ln(b) and log(A, k) with constant k as ln(k)/ln(A).
export function logsToLn(u, x) {
  return X.mapTree(u, (w) => {
    if (w.k === "fn" && w.name === "log" && w.args.length === 2 && depends(w, x)) return X.div(X.fn("ln", w.args[1]), X.fn("ln", w.args[0]));
    if (w.k === "fn" && w.name === "log" && w.args.length === 1 && depends(w, x)) return X.div(X.fn("ln", w.args[0]), X.fn("ln", num(10)));
    return w;
  });
}
// Perfect-power decomposition of a positive rational base: b = B^k with B minimal (integers or 1/integers).
function basePower(b) {
  if (b === X.E) return { B: X.E, k: Q.ONE };
  if (!X.isNum(b) || !Q.isPos(b.v) || Q.isOne(b.v)) return null;
  let { n, d } = b.v;
  let sign = 1n;
  if (n === 1n && d > 1n) { n = d; d = 1n; sign = -1n; }
  if (d !== 1n) return { B: b, k: Q.ONE };
  for (let k = 64n; k >= 2n; k--) {
    const [r, exact] = Q.iroot(n, Number(k));
    if (exact && r > 1n) return { B: X.num(Q.Q(r)), k: Q.Q(k * sign) };
  }
  return { B: X.num(Q.Q(n)), k: Q.Q(sign) };
}
function expAtoms(u, x) { return findAll(u, (w) => w.k === "pow" && !depends(w.args[0], x) && depends(w.args[1], x)); }
function kernelSubstitute(e, S, sub) {
  const x = S.x, dom = S.domain;
  let u = C(logsToLn(e, x), dom);
  const exps = expAtoms(u, x);
  const tn = fresh("τ", u);
  const t = X.sym(tn);
  let kernel = null, gt = null, positive = false, kernelWhy = "";
  if (exps.length) {
    // exponents must be rational multiples of one x-part T, bases powers of a common base
    const parts = exps.map((w) => {
      const [bse, A] = w.args;
      const [xs, cs] = xTerms(C(A, dom), x);
      return { w, bp: basePower(bse), T: C(X.add(...xs), dom), beta: C(X.add(...cs), dom) };
    });
    if (parts.some((p) => !p.bp)) return null;
    const B0 = parts[0].bp.B;
    if (!parts.every((p) => p.bp.B === B0)) return null;
    const T0 = parts[0].T;
    const ratios = parts.map((p) => C(X.div(p.T, T0), dom));
    if (!ratios.every(X.isNum)) return null;
    const ms = parts.map((p, i) => Q.mul(p.bp.k, ratios[i].v)); // term = B0^(beta k) * B0^(m T0)
    // g = gcd of the rationals ms
    let gn = 0n, gd = 1n;
    for (const m of ms) { gn = Q.bgcd(gn, m.n); gd = gd * m.d / Q.bgcd(gd, m.d); }
    const g = Q.Q(gn, gd);
    kernel = C(X.pow(B0, X.mul(X.num(g), T0)), dom);
    gt = u;
    parts.forEach((p, i) => { gt = X.replace(gt, p.w, X.mul(X.pow(p.bp.B, X.mul(X.num(p.bp.k), p.beta)), X.pow(t, X.num(Q.div(ms[i], g))))); });
    gt = C(gt, dom);
    positive = true;
    kernelWhy = `Every exponential term is a power of t = ${toText(kernel)}.`;
  } else {
    // one repeated non-polynomial atom (ln(A), ...)
    const atoms = findAll(u, (w) => w.k === "fn" && depends(w, x) && ["ln", "exp", "atan", "asin", "acos", "asinh", "acosh", "atanh"].includes(w.name));
    if (atoms.length !== 1) return null;
    kernel = atoms[0];
    gt = C(X.replace(u, kernel, t), dom);
    kernelWhy = `The unknown appears only through ${toText(kernel)}.`;
  }
  if (depends(gt, x)) return null;
  if (!X.hasSym(gt, tn)) return null;
  { const cg = coeffTrees(gt, tn); if (cg && cg.length === 2 && (exps.length <= 1)) return null; } // nothing gained
  S.log.add({ rule: "solve.substitute", title: `Substitute t = ${toText(kernel)}`, why: kernelWhy + (positive ? " Since t > 0, only positive roots in t are kept." : ""), before: X.eq(e, X.ZERO), after: X.eq(X.subs(gt, { [tn]: X.sym("t") }), X.ZERO) });
  const inner = sub(gt, { x: tn, allowNumeric: false });
  if (inner.approx.length || inner.general.length || inner.regions.length || inner.all) throw fail("the substituted equation has no exact solution");
  let out = emptySol();
  out.methods.push("substitution");
  for (const r of inner.exact) {
    if (positive) {
      const s = signConst(r.tree, dom);
      if (s === null) throw fail("could not decide the sign of a root");
      if (s <= 0) { S.log.add({ rule: "solve.substitute.reject", title: `Discard t = ${toText(r.tree)}`, why: `${toText(kernel)} is always positive.`, before: null, after: null, kind: "note" }); continue; }
    }
    const back = S.log.group({ rule: "solve.substitute.back", title: `Solve ${toText(kernel)} = ${toText(r.tree)}`, why: "Undo the substitution.", before: X.eq(kernel, r.tree), after: null }, () => sub(X.sub(kernel, r.tree)));
    out = mergeSol(out, back);
  }
  out.complete = out.complete && inner.complete;
  return out;
}

// ---------------------------------------------------------------- A b^f = B c^g  ->  logarithms
function expProductTerm(tm, x) {
  // c * prod b_j^(A_j): all x-dependence inside exponents with constant positive bases
  const fs = tm.k === "mul" ? tm.args : [tm];
  const coef = [], exps = [];
  for (const f of fs) {
    if (!depends(f, x)) coef.push(f);
    else if (f.k === "pow" && !depends(f.args[0], x)) exps.push(f);
    else return null;
  }
  return { c: X.mul(...coef), exps };
}
function expLogBothSides(e, S, sub) {
  const x = S.x, dom = S.domain;
  const terms = e.k === "add" ? e.args : [e];
  const xs = terms.filter((t) => depends(t, x)), cs = terms.filter((t) => !depends(t, x));
  let T1, T2;
  if (xs.length === 2 && !cs.length) { T1 = expProductTerm(xs[0], x); T2 = expProductTerm(xs[1], x); }
  else if (xs.length === 1) { T1 = expProductTerm(xs[0], x); T2 = { c: C(X.add(...cs), dom), exps: [] }; }
  else return null;
  if (!T1 || !T2 || !T1.exps.length) return null;
  if (![...T1.exps, ...T2.exps].every((w) => signConst(w.args[0], dom) === 1)) return null;
  // T1 = -T2
  const c1 = C(T1.c, dom), c2 = C(X.neg(T2.c), dom);
  const s1 = signConst(c1, dom), s2 = signConst(c2, dom);
  if (!s1 || s2 === null) return null;
  const lhs = C(X.mul(c1, ...T1.exps), dom), rhs = C(X.mul(c2, ...T2.exps), dom);
  if (s2 === 0 || s1 !== s2) {
    S.log.add({ rule: "solve.exp.sign", title: "Compare signs", why: `${toText(lhs)} and ${toText(rhs)} ${s2 === 0 ? "cannot be 0: exponentials are positive" : "have opposite signs for every x (exponentials are positive)"}.`, before: X.eq(lhs, rhs), after: X.FALSE });
    const out = emptySol(); out.methods.push("exponential"); out.notes.push("the two sides always have opposite signs"); return out;
  }
  const lnSide = (c, exps) => X.add(X.fn("ln", s1 < 0 ? C(X.neg(c), dom) : c), ...exps.map((w) => X.mul(w.args[1], X.fn("ln", w.args[0]))));
  const L = C(lnSide(c1, T1.exps), dom), R = C(lnSide(c2, T2.exps), dom);
  S.log.add({ rule: "solve.exp.log-both-sides", title: "Take the natural logarithm of both sides", why: "Both sides are positive, and ln is one-to-one, so this is an equivalence. ln(a b^u) = ln a + u ln b.", before: X.eq(lhs, rhs), after: X.eq(L, R) });
  const E = C(X.sub(L, R), dom);
  if (expAtoms(E, x).length) return null;
  const r = sub(E);
  r.methods.push("exponential");
  return r;
}

// ---------------------------------------------------------------- combine logarithms
function combineLogs(e, S, sub) {
  const x = S.x, dom = S.domain;
  const u = C(logsToLn(e, x), dom);
  const terms = u.k === "add" ? u.args : [u];
  const logs = [], rest = [];
  for (const tm of terms) {
    if (!depends(tm, x)) { rest.push(tm); continue; }
    const fs = tm.k === "mul" ? tm.args : [tm];
    const lnF = fs.filter((f) => f.k === "fn" && f.name === "ln" && depends(f, x));
    const others = fs.filter((f) => !(f.k === "fn" && f.name === "ln" && depends(f, x)));
    if (lnF.length !== 1 || others.some((f) => depends(f, x))) return null;
    logs.push({ k: C(X.mul(...others), dom), A: lnF[0].args[0] });
  }
  if (logs.length < 2 && !(logs.length === 1 && rest.length)) return null;
  if (logs.length < 2) return null; // single log is handled by isolation
  const lam = logs[0].k;
  const rs = logs.map((l) => tidy(X.div(l.k, lam), dom));
  if (!rs.every(X.isNum)) return null;
  let L = 1n;
  for (const r of rs) L = L * r.v.d / Q.bgcd(L, r.v.d);
  const R0 = tidy(X.div(X.neg(X.add(...rest)), lam), dom); // sum r_i ln A_i = R0
  const prod = C(X.mul(...logs.map((l, i) => X.pow(l.A, rs[i]))), dom);
  S.log.add({ rule: "solve.log.combine", title: "Combine the logarithms", why: "ln a + ln b = ln(ab) and k ln a = ln(a^k) on the domain where every logarithm is defined; values outside that domain are rejected afterwards.", before: X.eq(u, X.ZERO), after: X.eq(X.fn("ln", prod), R0), kind: "conditional" });
  const K = tidy(X.pow(X.E, R0), dom);
  S.log.add({ rule: "solve.log.exponentiate", title: "Exponentiate both sides", why: "ln A = c means A = e^c.", before: X.eq(X.fn("ln", prod), R0), after: X.eq(prod, K) });
  let E = X.sub(prod, K);
  if (L > 1n) {
    E = X.sub(C(X.pow(prod, X.num(Q.Q(L))), dom), C(X.pow(K, X.num(Q.Q(L))), dom));
    S.log.add({ rule: "solve.log.power", title: `Raise both sides to the power ${L}`, why: "Clears the fractional exponents; extra candidates are removed by the final check.", before: X.eq(prod, K), after: X.eq(C(X.pow(prod, X.num(Q.Q(L))), dom), C(X.pow(K, X.num(Q.Q(L))), dom)), kind: "conditional" });
  }
  const r = sub(C(E, dom));
  r.methods.push("logarithmic");
  return r;
}
