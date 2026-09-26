// Function analysis, analytic geometry and integral applications (call forms).
//
//   domain(f, x)            range(f, x)             zeros(f, x)            intercepts(f, x)
//   asymptotes(f, x)        critical(f, x)          extrema(f, x[, a, b])  inflection(f, x)
//   monotonic(f, x)         tangent(f, x, a)        normal(f, x, a)        inverse(f, x)
//   completesquare(p, x)    apart(p, x)             identity(lhs = rhs) | identity(lhs, rhs)
//   line(x1, y1, x2, y2)    slope(...)              distance(...)          midpoint(...)
//   arclength(f, x, a, b)   areabetween(f, g, x[, a, b])   volume(f, x, a, b)   avgvalue(f, x, a, b)
//
// Every command derives its answer with the symbolic engines (domain inference, the equation and
// inequality solvers, limits, derivatives, the integrator) and verifies it against the ORIGINAL
// input by a different method (dense sampling, one-sided numeric limits, central differences,
// independent quadrature, substitution, expansion back). A check that cannot be completed never
// counts as a pass: a result whose checks are all inconclusive is withheld. Commands refuse
// (UNSUPPORTED) rather than guess when a question is not decidable with these methods.
//
// The helper modules live in ../analysis/.

import * as X from "../expr.js";
import { parseDetailed } from "../parse.js";
import { makeCtx } from "../simplify.js";
import { StepLog } from "../steps.js";
import { register, toContractVerification, unsupported } from "../orchestrate.js";
import { cmdDomain, cmdRange, cmdZeros, cmdIntercepts, cmdAsymptotes, cmdCritical, cmdExtrema, cmdInflection, cmdMonotonic, cmdTangentNormal } from "../analysis/features.js";
import { cmdInverse } from "../analysis/inverse.js";
import { cmdCompleteSquare, cmdApart, cmdIdentity, cmdLine, cmdSlope, cmdDistance, cmdMidpoint, cmdArclength, cmdAreaBetween, cmdVolume, cmdAvgValue } from "../analysis/misc.js";

const HANDLERS = {
  domain: cmdDomain, range: cmdRange, zeros: cmdZeros, intercepts: cmdIntercepts, asymptotes: cmdAsymptotes,
  critical: cmdCritical, extrema: cmdExtrema, inflection: cmdInflection, monotonic: cmdMonotonic,
  tangent: cmdTangentNormal("tangent"), normal: cmdTangentNormal("normal"), inverse: cmdInverse,
  completesquare: cmdCompleteSquare, apart: cmdApart, identity: cmdIdentity,
  line: cmdLine, slope: cmdSlope, distance: cmdDistance, midpoint: cmdMidpoint,
  arclength: cmdArclength, areabetween: cmdAreaBetween, volume: cmdVolume, avgvalue: cmdAvgValue,
};
export const analysisCommands = Object.keys(HANDLERS);

const PASSTHROUGH = ["UNSUPPORTED", "TIMEOUT", "BUDGET"];
// verification policy: a crash or an all-inconclusive verification withholds the answer
function strictVerify(inner) {
  return (c) => {
    let v;
    try { v = inner(c); } catch (e) {
      if (e && e.code === "TIMEOUT") throw e;
      return { status: "failed", level: "numeric", checks: [{ name: "verification", method: "error", passed: false, detail: `verification could not be completed (${e && e.message}); the answer is withheld` }] };
    }
    if (!v) return { status: "failed", level: "numeric", checks: [{ name: "verification", method: "none", passed: false, detail: "no verification was produced" }] };
    if (v.status !== "failed" && !v.checks.some((k) => k.passed)) return { ...v, status: "failed", checks: [...v.checks, { name: "policy", method: "exact", passed: false, detail: "no check could confirm the answer, so it is withheld" }] };
    return v;
  };
}
function runCommand(name, node, env) {
  let c;
  try { c = HANDLERS[name](node, env); } catch (e) {
    if (e && PASSTHROUGH.includes(e.code)) throw e;
    if (e && e.code) throw unsupported(e.message);
    throw e;
  }
  if (!c) return null;
  c.verify = strictVerify(c.verify || (() => null));
  return c;
}

for (const name of analysisCommands) {
  register({
    // ahead of solve.optimize (priority 6), which also claims the goal "extrema" but only for
    // optimisation phrasings; if this strategy refuses the other one still gets its turn
    id: `analysis.${name}`, kinds: ["command"], priority: 4,
    applies: (card) => card.command === name,
    run: (node, card, env) => runCommand(name, node, env),
  });
}

// Direct runner (tests and callers that already hold the arguments): mirrors the orchestrator's
// contract for one command, including the rule that a failed verification is never reported.
export function runAnalysis(name, args, options = {}) {
  if (!HANDLERS[name]) throw new Error(`unknown analysis command ${name}`);
  const t0 = Date.now();
  const deadline = t0 + (options.timeLimit || 8000);
  const node = X.fn(name, ...args.map((a) => (typeof a === "string" ? parseDetailed(a).node : typeof a === "number" ? X.num(a) : a)));
  const log = new StepLog();
  const ctx = makeCtx({ domain: "real", conditions: [], budget: { ops: options.ops || 3_000_000 } });
  const env = { ctx, log, domain: "real", deadline, digits: options.digits || 20, options, original: node,
    checkTime() { if (Date.now() > deadline) { const e = new Error("time limit"); e.code = "TIMEOUT"; throw e; } } };
  const base = { ok: false, input: { tree: node }, answers: [], steps: [], conditions: [], rejected: [], solutionStatus: "unsolved", verification: { status: "not-applicable", checks: [] }, method: `analysis.${name}` };
  let c;
  try { c = runCommand(name, node, env); } catch (e) {
    if (!(e && e.code) && options.debug) throw e;
    return { ...base, solutionStatus: "unsupported", error: { message: e && e.message, code: e && e.code }, answers: [{ kind: "none", label: e && e.code ? e.message : `internal error: ${e && e.message}` }] };
  }
  if (!c) return { ...base, solutionStatus: "unsupported", answers: [{ kind: "none", label: "not applicable" }] };
  const verification = c.verify(c);
  const conditions = [];
  for (const k of [...(c.conditions || []), ...ctx.conditions]) if (k && k.k && !conditions.includes(k)) conditions.push(k);
  if (verification.status === "failed") return { ...base, solutionStatus: "unsolved", verification, answers: [{ kind: "none", label: "No method produced an answer that passed verification. Quelvra does not guess." }], withheld: c.answers };
  return { ...base, ok: true, answers: c.answers, steps: c.steps || log.steps, conditions, rejected: c.rejected || [], graph: c.graph || null,
    solutionStatus: c.solutionStatus || "exact", verification, note: c.note || "", ms: Date.now() - t0 };
}

export { toContractVerification };
