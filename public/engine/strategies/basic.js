// Built-in strategies: evaluation, simplification and differentiation.
// Equation, calculus and domain-specific solver families register themselves in their own files.

import * as X from "../expr.js";
import * as N from "../num.js";
import { simplify, expand, together, makeCtx } from "../simplify.js";
import { toText } from "../print.js";
import { diff } from "../calc/diff.js";
import { equivalent, verifyDerivative, evalC } from "../verify.js";
import { DISCRETE_NAMES } from "../discrete.js";
import { register, toContractVerification, unsupported } from "../orchestrate.js";
import { rationalize, simplifyFull, expandTrig, expandLog, contractLog } from "../rules.js";

let approxHook = null;
// The numerical engine installs a function (tree, digits) -> Approx record.
export function setApproxHook(fn) { approxHook = fn; }
export function approxOf(tree, digits) {
  if (X.isNum(tree)) {
    return { value: N.toDecimalString(tree.v, digits), digits, requested: digits, errorBound: tree.v.d === 1n ? "0" : `5e-${digits + 1}`, method: "exact-rational", iterations: 0, converged: true };
  }
  return approxHook ? approxHook(tree, digits) : null;
}

function exactAndApprox(tree, digits) {
  const answers = [{ kind: "exact", tree }];
  const isInteger = X.isNum(tree) && tree.v.d === 1n;
  if (!isInteger && X.freeSymbols(tree).size === 0 && tree !== X.UNDEF) {
    const a = approxOf(tree, digits);
    if (a) answers.push({ kind: "approx", approx: a });
  }
  return answers;
}

// Exact Gaussian-rational arithmetic: a tree built only from rationals, i, +, * and integer powers
// becomes [re, im] (rationals), or null for anything else (radicals, pi, functions, ...).
function gaussian(u, budget = { n: 0 }) {
  if (++budget.n > 5000) return null;
  if (X.isNum(u)) return [u.v, N.ZERO];
  if (u === X.I) return [N.ZERO, N.ONE];
  const kids = () => { const out = []; for (const a of u.args) { const g = gaussian(a, budget); if (!g) return null; out.push(g); } return out; };
  if (u.k === "add") { const g = kids(); return g && g.reduce(([a, b], [c, d]) => [N.add(a, c), N.add(b, d)], [N.ZERO, N.ZERO]); }
  if (u.k === "mul") { const g = kids(); return g && g.reduce(gmul, [N.ONE, N.ZERO]); }
  if (u.k === "pow" && X.isInt(u.args[1]) && u.args[1].v.n >= -64n && u.args[1].v.n <= 64n) {
    let b = gaussian(u.args[0], budget);
    if (!b) return null;
    let e = u.args[1].v.n;
    if (e < 0n) {
      const d = N.add(N.mul(b[0], b[0]), N.mul(b[1], b[1]));
      if (N.isZero(d)) return null;
      b = [N.div(b[0], d), N.div(N.neg(b[1]), d)];
      e = -e;
    }
    let r = [N.ONE, N.ZERO];
    for (let i = 0n; i < e; i++) r = gmul(r, b);
    return r;
  }
  return null;
}
const gmul = ([a, b], [c, d]) => [N.sub(N.mul(a, c), N.mul(b, d)), N.add(N.mul(a, d), N.mul(b, c))];

const usesFn = (u, names) => (u.k === "fn" && names.has(u.name)) || (u.args || []).some((a) => a && a.k && usesFn(a, names));
const CROSS_CHECK = new Set([...DISCRETE_NAMES, "binomial", "nCr", "nPr", "conj", "re", "im", "abs"]);

register({
  id: "evaluate.exact", kinds: ["arithmetic"], priority: 10,
  run(node, card, env) {
    // simplify(...) / expand(...) around a constant: evaluate the inside, never echo the command
    const cmd = node.k === "fn" && ["simplify", "expand"].includes(node.name) && node.args.length === 1 ? node.name : null;
    if (cmd) node = node.args[0];
    const before = node;
    let v = simplify(node, env.ctx);
    // conj / re / im / abs of an exact Gaussian rational: evaluate from its parts
    const PARTS = new Set(["conj", "re", "im", "abs"]);
    if (usesFn(v, PARTS)) {
      v = simplify(X.mapTree(v, (w) => {
        if (w.k !== "fn" || !PARTS.has(w.name) || w.args.length !== 1) return w;
        const g = gaussian(simplify(w.args[0], env.ctx));
        if (!g) return w;
        const [a, b] = g.map((q) => X.num(q));
        return w.name === "conj" ? X.add(a, X.mul(X.NEG_ONE, b, X.I)) : w.name === "re" ? a : w.name === "im" ? b : X.pow(X.add(X.pow(a, X.TWO), X.pow(b, X.TWO)), X.HALF);
      }), env.ctx);
      // an unevaluated part of a constant would only echo the input
      if (usesFn(v, new Set(["conj", "re", "im"]))) return null;
    }
    if (X.contains(v, X.I)) {
      // write exact complex numbers as a + bi
      const g = gaussian(v);
      if (g) v = simplify(X.add(X.num(g[0]), X.mul(X.num(g[1]), X.I)));
    }
    if (v !== before) env.log.add({ rule: "simp.evaluate", title: "Evaluate exactly", why: "Exact arithmetic on rationals, radicals and known constants.", before, after: v });
    if (cmd === "expand") { try { v = expand(v, env.ctx); } catch (e) { if (e.code !== "BUDGET") throw e; } }
    else if (cmd === "simplify" && v !== X.UNDEF) {
      // rationalise the denominator (1/(1 + sqrt(2)) -> sqrt(2) - 1), keeping the smallest equal form
      try {
        const r = rationalize(v);
        if (r && r.result && !r.stopped && !(r.conditions || []).length && r.result !== v) {
          let best = r.result;
          try { const e = expand(best, env.ctx); if (X.size(e) < X.size(best)) best = e; } catch (e) { if (e.code !== "BUDGET") throw e; }
          env.log.add({ rule: "rad.rationalize", title: "Rationalise the denominator", why: "Multiply the top and bottom by the conjugate so no root is left in the denominator.", before: v, after: best });
          v = best;
        }
      } catch (_) { /* keep the evaluated form */ }
    }
    if (v === X.UNDEF) return { answers: [{ kind: "none", label: "undefined" }], solutionStatus: "exact", note: "the expression is undefined", verify: () => ({ status: "not-applicable", checks: [] }) };
    return {
      answers: exactAndApprox(v, env.digits), solutionStatus: "exact",
      verify: () => {
        // independent: the verifier's own float evaluator vs the result
        const r = equivalent(node, v, { vars: [] });
        // equivalent() may answer "exact" by simplifying input - result, which re-runs the solver's own
        // evaluation of counting / probability functions; for those also compare the verifier's floats
        if ((r.status === "equivalent-exact" && usesFn(node, CROSS_CHECK)) || (r.status === "inconclusive" && X.contains(node, X.I))) {
          const a = evalC(node, {}, "complex"), b = evalC(v, {}, "complex");
          const ok = Number.isFinite(a.re) && Number.isFinite(a.im) && Math.hypot(a.re - b.re, a.im - b.im) <= 1e-9 * Math.max(1, Math.hypot(b.re, b.im));
          if (!ok) r.status = Number.isFinite(a.re) ? "different" : "inconclusive";
          else if (r.status === "inconclusive") r.status = "equivalent-numeric";
        }
        return toContractVerification([{ status: r.status === "equivalent-exact" ? "verified-exact" : r.status === "equivalent-numeric" ? "verified-numeric" : r.status === "different" ? "failed" : "inconclusive",
          checks: [{ kind: "re-evaluate", ok: r.status !== "different", detail: r.status === "different" ? "independent evaluation disagrees" : "independent floating-point evaluation of the input agrees with the result" }] }]);
      },
    };
  },
});

function simplifyLike(goal) {
  return (node, card, env) => {
    let u = node;
    if (u.k === "fn" && ["simplify", "expand", "factor"].includes(u.name)) u = u.args[0];
    const s = simplify(u, env.ctx);
    let r = s;
    let conditions = [];
    if (goal === "expand") {
      r = expand(s, env.ctx);
      // angle-addition / multiple-angle and logarithm expansion (rule sets; conditions kept)
      const hasFn = (t, names) => t.k === "fn" && names.includes(t.name) || (t.args || []).some((a) => a && a.k && hasFn(a, names));
      for (const [names, fn] of [[["sin", "cos", "tan"], expandTrig], [["log", "ln"], expandLog]]) {
        if (!hasFn(r, names)) continue;
        try {
          const e = fn(r, { ctx: env.ctx, allowConditional: true });
          if (e && e.result && e.result !== r && e.stopped !== "error") {
            let out = e.result;
            try { out = expand(out, env.ctx); } catch (err) { if (err.code !== "BUDGET") throw err; }
            r = out; conditions = conditions.concat(e.conditions || []);
          }
        } catch (err) { if (err.code !== "BUDGET") throw err; }
      }
    } else {
      // prefer the smallest equal form among the canonical, expanded and combined forms
      for (const alt of [() => expand(s, env.ctx), () => together(s, env.ctx)]) {
        try { const a = alt(); if (X.size(a) < X.size(r)) r = a; } catch (e) { if (e.code !== "BUDGET") throw e; }
      }
      // identities (Pythagorean, double angle, log and exponent laws) that need no extra assumptions
      try {
        const f = simplifyFull(r, { ctx: env.ctx });
        if (f && f.result && !(f.conditions || []).length && X.size(f.result) < X.size(r)) {
          for (const st of f.steps || []) if (st.rule !== "simplify.canonical") env.log.add({ rule: st.rule, title: st.title, why: st.why, before: st.before, after: st.after });
          r = f.result;
        }
      } catch (e) { if (e.code !== "BUDGET") throw e; }
    }
    if (goal === "factor") throw unsupported("factoring needs the polynomial engine");
    if (r !== u) env.log.add({ rule: goal === "expand" ? "expand" : "simp", title: goal === "expand" ? "Expand" : "Simplify", why: goal === "expand" ? "Multiply out every bracket and collect like terms." : "Combine like terms and like powers, and evaluate exact values.", before: u, after: r });
    return {
      answers: [{ kind: "exact", tree: r }], solutionStatus: "exact", ...(conditions.length ? { conditions } : {}),
      verify: () => {
        const e = equivalent(u, r);
        return toContractVerification([{ status: e.status === "equivalent-exact" ? "verified-exact" : e.status === "equivalent-numeric" ? "verified-numeric" : e.status === "different" ? "failed" : "inconclusive",
          checks: [{ kind: "equivalence", ok: e.status !== "different", detail: e.status === "equivalent-numeric" ? `input and result agree at ${e.tested} random points` : e.status === "equivalent-exact" ? "input minus result simplifies to 0" : e.status === "different" ? "input and result differ" : "could not compare" }] }]);
      },
    };
  };
}
register({ id: "simplify", kinds: ["expression"], goals: ["simplify", "evaluate"], priority: 20, run: simplifyLike("simplify") });
register({ id: "expand", kinds: ["expression"], goals: ["expand"], priority: 20, run: simplifyLike("expand") });
// "condense 2 ln x + ln y": combine logarithms into one (the contraction rules keep their conditions)
register({
  id: "condense", kinds: ["expression", "arithmetic"], goals: ["condense"], priority: 5,
  run(node, card, env) {
    const u = simplify(node, env.ctx);
    const r = contractLog(u, { ctx: env.ctx, allowConditional: true });
    if (!r || !r.result || r.result === u || r.stopped === "error") return null;
    for (const st of r.steps || []) env.log.add({ rule: st.rule, title: st.title, why: st.why, before: st.before, after: st.after, conditions: st.conditions });
    const conds = r.conditions || [];
    return {
      answers: [{ kind: "exact", tree: r.result }], solutionStatus: "exact", ...(conds.length ? { conditions: conds } : {}),
      verify: () => {
        const e = equivalent(u, r.result);
        return toContractVerification([{ status: e.status === "equivalent-exact" ? "verified-exact" : e.status === "equivalent-numeric" ? "verified-numeric" : e.status === "different" ? "failed" : "inconclusive",
          checks: [{ kind: "equivalence", ok: e.status !== "different", detail: "the condensed form agrees with the input wherever both are defined" }] }]);
      },
    };
  },
});

register({
  id: "differentiate", kinds: ["derivative"], priority: 10,
  run(node, card, env) {
    const [u, x] = node.args;
    const order = node.args[2] && X.isNum(node.args[2]) ? Number(node.args[2].v.n) : 1;
    let d = diff(u, x, { order, steps: env.log, ctx: env.ctx });
    if (order > 1) { try { const e = expand(d, env.ctx); if (X.size(e) < X.size(d)) d = e; } catch (err) { if (err.code !== "BUDGET") throw err; } }
    return {
      answers: [{ kind: "exact", tree: d }], solutionStatus: "exact",
      graph: { exprs: X.freeSymbols(u).size <= 1 ? [u, d] : [], marks: [] },
      verify: () => {
        if (order === 1) return toContractVerification([verifyDerivative(u, d, x.name)]);
        if (!(order >= 2 && order <= 6)) return { status: "not-applicable", checks: [] };
        // higher order: every link u -> u' -> u'' ... is checked by the verifier's own central
        // differences, and the answer must equal the last link
        const results = [];
        let prev = u;
        for (let k = 1; k <= order; k++) {
          const next = diff(prev, x, { order: 1, ctx: env.ctx });
          results.push(verifyDerivative(prev, next, x.name));
          prev = next;
        }
        const e = equivalent(prev, d);
        results.push({ status: e.status === "equivalent-exact" ? "verified-exact" : e.status === "equivalent-numeric" ? "verified-numeric" : e.status === "different" ? "failed" : "inconclusive",
          checks: [{ kind: "chain", ok: e.status !== "different", detail: `the answer equals the ${order}-fold derivative built one checked step at a time` }] });
        return toContractVerification(results);
      },
    };
  },
});
