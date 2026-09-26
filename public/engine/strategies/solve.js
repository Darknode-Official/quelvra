// Quelvra solver strategies (equations, inequalities, systems, integer problems, extrema).
// Importing this module registers every strategy with the orchestrator.
//
// Primary strategies run the exact engine in engine/solve/; cross-check strategies (crossCheck:
// true) solve the same problem by an independent method (certified numerics, Groebner bases,
// substitution) and the orchestrator compares the two answers.

import * as X from "../expr.js";
import { register, toContractVerification } from "../orchestrate.js";
import { toText } from "../print.js";
import { unwrap, passCheck, signConst, C } from "../solve/util.js";
import { solveEquation } from "../solve/equation.js";
import { solveInequality } from "../solve/inequality.js";
import { solveLinearSystem, solvePolySystem, solveBySubstitution } from "../solve/system.js";
import { solveInteger, integerMode } from "../solve/integer.js";
import { solveOptimize, isOptimizeGoal } from "../solve/optimize.js";

const EQ = ["equation"];
const eqFamilies = {
  "solve.linear": ["linear"],
  "solve.quadratic": ["quadratic"],
  "solve.polynomial": ["cubic", "quartic", "polynomial"],
  "solve.rational": ["rational"],
  "solve.radical": ["radical"],
  "solve.abs": ["absolute-value"],
  "solve.exponential": ["exponential"],
  "solve.logarithmic": ["logarithmic"],
  "solve.trig": ["trigonometric"],
  "solve.hyperbolic": ["hyperbolic"],
  "solve.transcendental": ["transcendental", "special"],
};
const ALL_EQ_FAMILIES = Object.values(eqFamilies).flat();
// CONTRACT puts noSolution on the result, but orchestrate.js copies only answers/status/extra;
// mirror the flag into extra so callers can read it (result.extra.noSolution).
const _register = register;
function reg(spec) {
  const run = spec.run;
  _register({ ...spec, run: (node, card, env) => {
    // integer mode is handled only by solve.integer: a real-number answer would be wrong there
    if (integerMode(env) && spec.id !== "solve.integer" && spec.id !== "solve.optimize" && X.freeSymbols(unwrap(node).node).size) return null;
    const c = run(node, card, env);
    if (c && c.noSolution) c.extra = { ...(c.extra || {}), noSolution: true };
    return c;
  } });
}

// integer mode and congruences first (they return null when not applicable)
reg({ id: "solve.integer", kinds: ["equation", "system"], priority: 5, run: (node, card, env) => solveInteger(node, card, env) });

// extrema of f(x)
reg({
  id: "solve.optimize", kinds: ["expression", "command"], priority: 6,
  applies: (card) => isOptimizeGoal(card.goal) || isOptimizeGoal(card.command) || isOptimizeGoal(card.family),
  run: (node, card, env) => solveOptimize(node, card, env),
});

// relations without the unknown: decide them exactly
reg({
  id: "solve.check", kinds: ["equation", "inequality"], families: ["constant"], priority: 8,
  run: (node, card, env) => {
    const { node: rel } = unwrap(node);
    if (rel.k !== "eq" && rel.k !== "rel") return null;
    // the unknown cancels (x + 1 = x + 2): the equation engine proves identity / contradiction
    if (X.freeSymbols(rel).size) return rel.k === "eq" ? solveEquation(node, card, env, "exact") : solveInequality(node, card, env, "exact");
    const d = C(X.sub(rel.args[0], rel.args[1]));
    const s = signConst(d);
    if (s === null) return null;
    const op = rel.k === "eq" ? "=" : rel.op;
    const holds = op === "=" ? s === 0 : op === "<" ? s < 0 : op === "<=" ? s <= 0 : op === ">" ? s > 0 : op === ">=" ? s >= 0 : s !== 0;
    env.log.add({ rule: "solve.check.constant", title: "Decide the relation", why: `${toText(rel.args[0])} - (${toText(rel.args[1])}) = ${toText(d)}, which is ${s === 0 ? "zero" : s > 0 ? "positive" : "negative"}.`, before: rel, after: holds ? X.TRUE : X.FALSE });
    const cand = { answers: [{ kind: "exact", tree: holds ? X.TRUE : X.FALSE }], solutionStatus: "exact", rejected: [], conditions: [], verify: () => toContractVerification([passCheck("exact-sign", `the difference ${toText(d)} has sign ${s}`)]) };
    cand.compare = () => true;
    return cand;
  },
});

// one equation, one unknown (all exact families share the engine; the id reflects the family)
for (const [id, families] of Object.entries(eqFamilies)) {
  reg({ id, kinds: EQ, families, priority: 10, run: (node, card, env) => solveEquation(node, card, env, "exact") });
}
// independent certified numeric root search (cross-check for every equation family)
reg({ id: "solve.numeric", kinds: EQ, families: ALL_EQ_FAMILIES, priority: 80, crossCheck: true, run: (node, card, env) => solveEquation(node, card, env, "numeric-check") });

// inequalities (single, compound, chained, systems of inequalities)
reg({ id: "solve.ineq", kinds: ["inequality", "system"], priority: 10, applies: (card) => card.kind === "inequality" || card.family === "inequality-system", run: (node, card, env) => solveInequality(node, card, env, "exact") });
reg({ id: "solve.ineq.numeric", kinds: ["inequality", "system"], priority: 80, crossCheck: true, applies: (card) => card.kind === "inequality" || card.family === "inequality-system", run: (node, card, env) => solveInequality(node, card, env, "numeric-check") });

// systems
reg({ id: "solve.linear-system", kinds: ["system"], families: ["linear-system"], priority: 10, run: (node, card, env) => solveLinearSystem(node, card, env) });
reg({ id: "solve.polysys", kinds: ["system"], families: ["linear-system", "nonlinear-system"], priority: 20, crossCheck: true, run: (node, card, env) => solvePolySystem(node, card, env) });
reg({ id: "solve.substitution", kinds: ["system"], families: ["linear-system", "nonlinear-system"], priority: 30, crossCheck: true, run: (node, card, env) => solveBySubstitution(node, card, env) });
