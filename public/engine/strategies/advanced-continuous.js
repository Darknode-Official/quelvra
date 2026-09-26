// Advanced continuous mathematics (call forms; plain English is translated to these by
// advanced/language-patterns.js):
//
//   multivariable : pdiff grad dirderiv jacobian jacobiandet hessian laplacian totaldiff tangentplane
//                   lagrange dblint tplint polarint cylint sphint, and critical/extrema for f(x, y, ...)
//   vector        : div curl lineint conservative potential surfint flux, arclength of r(t)
//   transforms    : laplace invlaplace lapsolve fourier fouriertransform ztransform
//   complex       : residue laurent contourint residueint analytic cauchyriemann
//   numerical     : newton bisection secant fixedpoint trapezoid simpson eulermethod rungekutta (RK4) poweriter
//   curves        : curvature torsion unittangent unitnormal binormal arcparam
//   PDE           : pdecheck classifypde heat wave
//
// Every command derives its answer symbolically (or by a labelled numerical method) and returns a
// verify() that checks it against the ORIGINAL input by an independent route: finite differences
// of the input, independent quadrature, contour integrals by the trapezoid rule, forward numeric
// transforms, exact substitution certificates. A crash or an all-inconclusive verification
// withholds the answer (the orchestrator never shows a failed verification).
// The helper modules live in ../advanced/.

import * as X from "../expr.js";
import { parseDetailed } from "../parse.js";
import { makeCtx } from "../simplify.js";
import { StepLog } from "../steps.js";
import { register, unsupported } from "../orchestrate.js";
import { MULTIVAR, multivarCritical, multivarCriticalApplies } from "../advanced/multivar.js";
import { MULTINT, nestedIntegral } from "../advanced/multint.js";
import { VECTOR, paramArclength } from "../advanced/vector.js";
import { TRANSFORMS } from "../advanced/transforms.js";
import { COMPLEX } from "../advanced/complex.js";
import { NUMERICAL } from "../advanced/numerical.js";
import { CURVES, graphCurvatureApplies } from "../advanced/curves.js";
import { PDE } from "../advanced/pde.js";

const HANDLERS = { ...MULTIVAR, ...MULTINT, ...VECTOR, ...TRANSFORMS, ...COMPLEX, ...NUMERICAL, ...CURVES, ...PDE };
export const advancedCommands = Object.keys(HANDLERS);

const PASSTHROUGH = ["UNSUPPORTED", "TIMEOUT", "BUDGET"];
function strictVerify(inner) {
  return (c) => {
    let v;
    try { v = inner(c); } catch (e) {
      if (e && e.code === "TIMEOUT") throw e;
      return { status: "failed", level: "numeric", checks: [{ name: "verification", method: "error", passed: false, detail: `verification could not be completed (${e && e.message}); the answer is withheld` }] };
    }
    if (!v) return { status: "failed", level: "numeric", checks: [{ name: "verification", method: "none", passed: false, detail: "no verification was produced" }] };
    if (v.status !== "failed" && !v.checks.some((k) => k.passed)) return { ...v, status: "failed", checks: [...v.checks, { name: "policy", method: "exact", passed: false, detail: "no check could confirm the answer, so it is withheld" }] };
    if (v.status === "partial") return { ...v, status: "failed", checks: [...v.checks, { name: "policy", method: "exact", passed: false, detail: "part of the answer could not be confirmed, so it is withheld" }] };
    return v;
  };
}
function wrap(fn, node, env) {
  let c;
  try { c = fn(node, env); } catch (e) {
    if (e && PASSTHROUGH.includes(e.code)) throw e;
    if (e && e.code) throw unsupported(e.message);
    throw e;
  }
  if (!c) return null;
  c.verify = strictVerify(c.verify || (() => null));
  return c;
}

for (const name of advancedCommands) {
  register({ id: `advanced.${name}`, kinds: ["command"], priority: 4, applies: (card) => card.command === name, run: (node, card, env) => wrap(HANDLERS[name], node, env) });
}
// multivariable critical points / extrema: ahead of the one-variable analysis commands, and only
// when the function has two or more variables (otherwise it steps aside)
for (const name of ["critical", "extrema"]) {
  register({ id: `advanced.${name}-multivariable`, kinds: ["command"], priority: 3, applies: (card) => card.command === name,
    run: (node, card, env) => (multivarCriticalApplies(node) ? wrap(multivarCritical, node, env) : null) });
}
// arc length of a parametrised curve r(t) = [x(t), y(t), ...]; curvature of y = f(x) is in CURVES
register({ id: "advanced.arclength-parametric", kinds: ["command"], priority: 3, applies: (card) => card.command === "arclength",
  run: (node, card, env) => (node.args[0] && (node.args[0].k === "vector" || node.args[0].k === "tuple") ? wrap(paramArclength, node, env) : null) });
void graphCurvatureApplies;
// iterated integrals written as nested integrate(...) calls
register({ id: "advanced.iterated-integral", kinds: ["integral"], priority: 2,
  run: (node, card, env) => (node.args[0] && node.args[0].k === "integral" ? wrap(nestedIntegral, node, env) : null) });

// Direct runner for tests: same contract as the orchestrator for one command.
export function runAdvanced(name, args, options = {}) {
  if (!HANDLERS[name]) throw new Error(`unknown advanced command ${name}`);
  const t0 = Date.now();
  const deadline = t0 + (options.timeLimit || 8000);
  const node = X.fn(name, ...args.map((a) => (typeof a === "string" ? parseDetailed(a).node : typeof a === "number" ? X.num(a) : a)));
  const log = new StepLog();
  const ctx = makeCtx({ domain: "real", conditions: [], budget: { ops: options.ops || 3_000_000 } });
  const env = { ctx, log, domain: "real", deadline, digits: options.digits || 20, options, original: node,
    checkTime() { if (Date.now() > deadline) { const e = new Error("time limit"); e.code = "TIMEOUT"; throw e; } } };
  let c;
  try { c = wrap(HANDLERS[name], node, env); } catch (e) {
    if (!(e && e.code) && options.debug) throw e;
    return { ok: false, solutionStatus: "unsupported", answers: [{ kind: "none", label: e && e.code ? e.message : `internal error: ${e && e.message}` }] };
  }
  if (!c) return { ok: false, answers: [{ kind: "none", label: "not applicable" }] };
  const verification = c.verify(c);
  if (verification.status === "failed") return { ok: false, solutionStatus: "unsolved", verification, answers: [{ kind: "none", label: "withheld" }], withheld: c.answers };
  return { ok: true, answers: c.answers, steps: c.steps || log.steps, verification, solutionStatus: c.solutionStatus || "exact", ms: Date.now() - t0 };
}
