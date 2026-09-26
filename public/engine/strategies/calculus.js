// Calculus strategies: limits, sums, products, series, recurrences and ODEs.
//
//   calc.limit       (kinds limit,  priority 10)  series / Gruntz (mrv) / squeeze / oscillation proofs,
//                                                 checked numerically along sequences
//   calc.sum         (kinds sum,    priority 10)  Faulhaber, Gosper, polynomial x geometric, zeta and
//                                                 digamma closed forms, convergence tests, power series
//   calc.product     (kinds product, priority 10) factorial / Gamma ratios, limits of partial products
//   calc.series      (command series / taylor, priority 10)  Taylor, Laurent, Puiseux expansions
//   calc.recurrence  (kinds system/equation, priority 2)     linear recurrences a(n), a(n-1), ...
//   calc.ode         (kinds equation/system, priority 3)     ODEs y', y'', dy/dx, ... with initial conditions
//
// The recurrence and ODE strategies return null at once when the input has no a(n +- k) pattern or
// no derivative of an unknown function, so ordinary equations pass straight through to the solver.
// ODE and recurrence answers that the substitution check cannot confirm are withheld, never reported.

import * as X from "../expr.js";
import { toText } from "../print.js";
import { register, toContractVerification, unsupported } from "../orchestrate.js";
import { limit as limitOf, verifyLimit, setPrinter as setLimitPrinter } from "../calc/limit.js";
import { seriesTree, verifySeries } from "../calc/series.js";
import { sumCompute, verifySum, productCompute, verifyProduct, setPrinter as setSumPrinter } from "../calc/sum.js";
import { detectRecurrence, solveRecurrence, verifyRecurrence, setPrinter as setRecurPrinter } from "../calc/recur.js";
import { detectODE, solveODE, verifyODE, setPrinter as setOdePrinter } from "../calc/ode.js";

setLimitPrinter(toText); setSumPrinter(toText); setRecurPrinter(toText); setOdePrinter(toText);

// the parser reads a typed C1 as the symbol C_1; answers use the same name so they can be pasted back
const CN = (u) => (u ? X.mapTree(u, (w) => (w.k === "sym" && /^C\d+$/.test(w.name) ? X.sym(`C_${w.name.slice(1)}`) : w)) : u);
const cName = (n) => (/^C\d+$/.test(n) ? `C_${n.slice(1)}` : n);
const now = () => (typeof performance !== "undefined" ? performance.now() : Date.now());
const V = (r) => toContractVerification([r]);
const strict = (r) => (r.status === "inconclusive" ? { ...r, status: "failed", checks: [...r.checks, { kind: "policy", ok: false, detail: "the answer could not be confirmed, so it is withheld" }] } : r);
const timeFor = (env, cap) => Math.max(400, Math.min(cap, env.deadline - now() - 300));
const pass = (e) => {
  if (e && ["UNSUPPORTED", "UNKNOWN", "UNDEFINED", "NOINTEGRAL", "INTERNAL", "NEEDMORE", "UNDECIDABLE", "COMPLEX", "SINGULAR", "BUDGET"].includes(e.code)) throw unsupported(e.message);
  throw e;
};

// ---------------------------------------------------------------- limits
register({
  id: "calc.limit", kinds: ["limit"], priority: 10,
  run(node, card, env) {
    const [u, x, to] = node.args;
    const dir = node.dir || "";
    const r = limitOf(u, x, to, dir, { log: env.log, timeLimit: timeFor(env, 9000) });
    if (r.status === "unknown") throw unsupported(r.reason || "Quelvra could not determine this limit.");
    const verify = () => V(verifyLimit(u, x, to, dir, r.result));
    if (r.status === "dne") {
      return { answers: [{ kind: "none", tree: X.UNDEF, label: "The limit does not exist", reason: r.reason }], solutionStatus: "exact", note: r.reason, extra: { method: r.method }, verify };
    }
    const notes = r.result && r.result.notes ? r.result.notes : [];
    return { answers: [{ kind: "exact", tree: r.value }], solutionStatus: "exact", note: notes.join(" "), extra: { method: r.method }, verify };
  },
});

// ---------------------------------------------------------------- sums and products
function sumLike(kind) {
  return (node, card, env) => {
    const [f, k, lo, hi] = node.args;
    let r;
    const opts = { timeLimit: timeFor(env, 12000) };
    try { r = kind === "sum" ? sumCompute(f, k, lo, hi, opts) : productCompute(f, k, lo, hi, opts); } catch (e) { pass(e); }
    const verify = () => V(kind === "sum" ? verifySum(f, k, lo, hi, r) : verifyProduct(f, k, lo, hi, r));
    const base = { steps: r.steps, conditions: r.conditions || [], extra: { method: r.method || null }, verify };
    if (r.kind === "diverges") {
      return { ...base, answers: [{ kind: "none", label: kind === "sum" ? "The series diverges" : "The product diverges", reason: r.reason }], solutionStatus: "exact", note: r.reason };
    }
    if (r.kind === "converges") {
      if (!r.approx) throw unsupported(`The series converges (${r.reason}), but Quelvra found no closed form or reliable numeric value.`);
      return { ...base, answers: [{ kind: "approx", label: "The series converges", approx: { value: r.approx, digits: r.digits || 20 }, reason: r.reason }], solutionStatus: "approximate", note: `Converges: ${r.reason}. No closed form was found; the value is numeric.` };
    }
    return { ...base, answers: [{ kind: "exact", tree: r.value }], solutionStatus: "exact", note: r.note || "" };
  };
}
register({ id: "calc.sum", kinds: ["sum"], priority: 10, run: sumLike("sum") });
register({ id: "calc.product", kinds: ["product"], priority: 10, run: sumLike("product") });

// ---------------------------------------------------------------- series command
// series(f, x, a, n): terms through (x - a)^n plus O((x - a)^(n+1)) (Mathematica convention);
// taylor(...) returns the Taylor polynomial alone. Defaults: x the only variable, a = 0, n = 5.
register({
  id: "calc.series", kinds: ["command"], priority: 10,
  applies: (card) => card.command === "series" || card.command === "taylor",
  run(node, card, env) {
    const args = node.args;
    if (!args.length) throw unsupported("series needs an expression");
    const u = args[0];
    let x = null, a = X.ZERO, n = 5;
    let rest = args.slice(1);
    if (rest[0] && rest[0].k === "eq" && rest[0].args[0].k === "sym") { x = rest[0].args[0]; a = rest[0].args[1]; rest = rest.slice(1); }
    else if (rest[0] && rest[0].k === "sym") { x = rest[0]; rest = rest.slice(1); if (rest.length >= 2) { a = rest[0]; rest = rest.slice(1); } }
    if (rest.length) {
      if (!X.isInt(rest[0]) || rest[0].v.n < 0n || rest[0].v.n > 60n) throw unsupported("the order must be a whole number between 0 and 60");
      n = Number(rest[0].v.n);
    }
    if (!x) {
      const fs = [...X.freeSymbols(u)];
      const pick = fs.length === 1 ? fs[0] : fs.includes("x") ? "x" : card.unknowns && card.unknowns[0];
      if (!pick) throw unsupported("series needs a variable");
      x = X.sym(pick);
    }
    let res;
    try { res = seriesTree(u, x, a, n + 1, {}); } catch (e) { pass(e); }
    const isTaylor = card.command === "taylor";
    if (isTaylor && res.terms.some((t) => t.e.d !== 1n || t.e.n < 0n)) throw unsupported("the expansion has negative or fractional powers, so it is not a Taylor polynomial; use series(...)");
    const tree = isTaylor ? res.main : res.tree;
    const where = a === X.OO ? "at infinity" : `about ${x.name} = ${toText(a)}`;
    env.log.add({ rule: "series.expand", title: isTaylor ? "Taylor polynomial" : "Series expansion", why: `Expand ${where} by composing the known series of the elementary functions (exact coefficients; the O-term bounds the remainder).`, before: u, after: tree });
    return {
      answers: [{ kind: "exact", tree }], solutionStatus: "exact",
      note: res.terms.some((t) => t.e.d !== 1n) ? "Puiseux series (fractional powers)." : res.terms.some((t) => t.e.n < 0n) ? "Laurent series (negative powers)." : "",
      verify: () => V(verifySeries(u, x, a, res)),
    };
  },
});

// ---------------------------------------------------------------- recurrences
register({
  id: "calc.recurrence", kinds: ["system", "equation"], priority: 2,
  run(node, card, env) {
    const info = detectRecurrence(node);
    if (!info) return null;
    let r;
    try { r = solveRecurrence(info, { timeLimit: timeFor(env, 10000) }); } catch (e) { pass(e); }
    const name = info.F || "a";
    const consts = (r.constants || []).map((c) => cName(c.name));
    return {
      answers: [{ kind: "exact", label: `${name}(${info.n})`, tree: CN(r.value) }], solutionStatus: "exact", steps: r.steps,
      note: consts.length ? `${consts.join(", ")} ${consts.length > 1 ? "are arbitrary constants" : "is an arbitrary constant"} (no initial conditions were given).` : "",
      extra: { method: r.method, kind: "recurrence" },
      verify: () => V(strict(verifyRecurrence(info, r))),
    };
  },
});

// ---------------------------------------------------------------- ODEs
register({
  id: "calc.ode", kinds: ["equation", "system"], priority: 3,
  run(node, card, env) {
    const info = detectODE(node);
    if (!info) return null;
    let r;
    try { r = solveODE(info, { timeLimit: timeFor(env, 12000) }); } catch (e) {
      if (e && e.code === "INCONSISTENT") return { answers: [{ kind: "none", label: "No solution satisfies the conditions", reason: e.message }], solutionStatus: "exact", noSolution: true, extra: { noSolution: true }, note: e.message, verify: () => ({ status: "not-applicable", checks: [] }) };
      pass(e);
    }
    const verify = () => V(strict(verifyODE(info, r)));
    if (r.approximate) {
      const dep = info.deps[0];
      return {
        answers: [{ kind: "approx", label: `${dep}(${+r.t1.toPrecision(12)})`, approx: { value: r.finalText || String(r.final), digits: 10 } }], solutionStatus: "approximate", steps: r.steps,
        note: "No closed-form method applied; the value comes from an adaptive numeric integration.", extra: { method: r.method, table: r.table }, verify,
      };
    }
    const answers = [];
    if (info.deps.length > 1) answers.push({ kind: "solution", values: info.deps.map((d) => [d, CN((r.solutions.find((s) => s.dep === d) || {}).tree)]) });
    else for (const s of r.solutions) {
      answers.push({ kind: "exact", label: s.kind === "implicit" ? `${s.dep} (implicit)` : s.singular ? `${s.dep} (constant solution)` : s.dep, tree: CN(s.tree) });
    }
    const unsolved = (r.constants || []).map((c) => c.name).filter((c) => !r.constantsSolved || !(c in r.constantsSolved)).map(cName);
    const notes = [];
    if (unsolved.length) notes.push(`${unsolved.join(", ")} ${unsolved.length > 1 ? "are arbitrary constants" : "is an arbitrary constant"}.`);
    return { answers, solutionStatus: "exact", steps: r.steps, conditions: r.conditions || [], note: notes.join(" "), extra: { method: r.method, kind: "ode", order: info.order }, verify };
  },
});
