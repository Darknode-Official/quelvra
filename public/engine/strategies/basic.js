// Built-in strategies: evaluation, simplification and differentiation.
// Equation, calculus and domain-specific solver families register themselves in their own files.

import * as X from "../expr.js";
import * as N from "../num.js";
import { simplify, expand, together, makeCtx } from "../simplify.js";
import { toText } from "../print.js";
import { diff } from "../calc/diff.js";
import { equivalent, verifyDerivative } from "../verify.js";
import { register, toContractVerification, unsupported } from "../orchestrate.js";
import { rationalize } from "../rules.js";

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

register({
  id: "evaluate.exact", kinds: ["arithmetic"], priority: 10,
  run(node, card, env) {
    // simplify(...) / expand(...) around a constant: evaluate the inside, never echo the command
    const cmd = node.k === "fn" && ["simplify", "expand"].includes(node.name) && node.args.length === 1 ? node.name : null;
    if (cmd) node = node.args[0];
    const before = node;
    let v = simplify(node, env.ctx);
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
    if (goal === "expand") r = expand(s, env.ctx);
    else {
      // prefer the smallest equal form among the canonical, expanded and combined forms
      for (const alt of [() => expand(s, env.ctx), () => together(s, env.ctx)]) {
        try { const a = alt(); if (X.size(a) < X.size(r)) r = a; } catch (e) { if (e.code !== "BUDGET") throw e; }
      }
    }
    if (goal === "factor") throw unsupported("factoring needs the polynomial engine");
    if (r !== u) env.log.add({ rule: goal === "expand" ? "expand" : "simp", title: goal === "expand" ? "Expand" : "Simplify", why: goal === "expand" ? "Multiply out every bracket and collect like terms." : "Combine like terms and like powers, and evaluate exact values.", before: u, after: r });
    return {
      answers: [{ kind: "exact", tree: r }], solutionStatus: "exact",
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

register({
  id: "differentiate", kinds: ["derivative"], priority: 10,
  run(node, card, env) {
    const [u, x] = node.args;
    const order = node.args[2] && X.isNum(node.args[2]) ? Number(node.args[2].v.n) : 1;
    const d = diff(u, x, { order, steps: env.log, ctx: env.ctx });
    return {
      answers: [{ kind: "exact", tree: d }], solutionStatus: "exact",
      graph: { exprs: X.freeSymbols(u).size <= 1 ? [u, d] : [], marks: [] },
      verify: () => {
        if (order !== 1) return { status: "not-applicable", checks: [] };
        return toContractVerification([verifyDerivative(u, d, x.name)]);
      },
    };
  },
});
