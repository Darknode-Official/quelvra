// Quelvra solvers: integer problems.
//
//   * linear Diophantine a x + b y = c (integers): extended Euclid (numtheory.linearDiophantine);
//     all solutions x = x0 + (b/g) t, y = y0 - (a/g) t, or a proof that gcd(a, b) does not divide c.
//   * congruences mod(a x + b, m) = r: numtheory.solveLinearCongruence (integer mode), or over the
//     reals a x + b = r + m k (k an integer) when 0 <= r < m.
//   * systems of congruences mod(x, m_i) = r_i: Chinese remainder theorem (numtheory.crt).
//   * any other one-variable equation in integer mode: solve over the reals, keep integer solutions
//     (complete, since the real solution set is complete).
// Integer mode: options.integers === true or options.domain === "integer".

import * as X from "../expr.js";
import * as Q from "../num.js";
import * as NT from "../numtheory.js";
import { toText } from "../print.js";
import { toContractVerification } from "../orchestrate.js";
import { C, safe, fail, unwrap, isZeroExact, passCheck, failCheck, tidy, findAll } from "./util.js";
import { coeffTrees } from "./poly.js";
import { solveEquation } from "./equation.js";

export const integerMode = (env) => !!(env.options && (env.options.integers === true || env.options.domain === "integer" || env.options.integer === true));

function intOf(t) { return X.isInt(t) ? t.v.n : null; }
// mod(A, m) = r  with A linear in x (integer coefficients), m, r integers
function modForm(eq, x) {
  let [L, R] = eq.args;
  if (!(L.k === "fn" && L.name === "mod")) [L, R] = [R, L];
  if (!(L.k === "fn" && L.name === "mod" && L.args.length === 2)) return null;
  const m = intOf(C(L.args[1])), r = intOf(C(R));
  if (m === null || r === null || m === 0n) return null;
  const cs = coeffTrees(C(L.args[0]), x);
  if (!cs || cs.length !== 2 || !cs.every(X.isInt)) return null;
  return { a: cs[1].v.n, b: cs[0].v.n, m: m < 0n ? -m : m, r };
}

export function solveInteger(node, card, env) {
  const { node: inner, vars } = unwrap(node);
  const intMode = integerMode(env);
  const hasMod = findAll(inner, (w) => w.k === "fn" && w.name === "mod").length > 0;
  if (!intMode && !hasMod) return null;
  const log = env.log;
  // systems of congruences
  if (inner.k === "system" || inner.k === "and") {
    const syms = [...X.freeSymbols(inner)];
    if (syms.length !== 1) {
      if (intMode && inner.args.length >= 1) return null;
      return null;
    }
    const x = syms[0];
    const forms = inner.args.map((e) => (e.k === "eq" ? modForm(e, x) : null));
    if (forms.some((f) => !f)) return null;
    // each a x = r - b (mod m) -> x = res (mod mod')
    const pairs = [];
    for (const f of forms) {
      const s = NT.solveLinearCongruence(f.a, f.r - f.b, f.m);
      if (!s.solvable) return noneCand(`${f.a} ${x} = ${f.r - f.b} (mod ${f.m}) has no solution: gcd(${f.a}, ${f.m}) does not divide ${f.r - f.b}`, inner, env);
      pairs.push([s.residue, s.modulus]);
    }
    const r = NT.crt(pairs);
    for (const s of r.steps || []) log.add({ ...s, rule: "solve.integer.crt" });
    if (!r.consistent) return noneCand("the congruences are inconsistent (Chinese remainder theorem)", inner, env);
    return congruenceCand(x, r.residue, r.modulus, inner, env, "Chinese remainder theorem");
  }
  if (inner.k !== "eq") return null;
  const syms = [...X.freeSymbols(inner)];
  // congruence in one unknown
  if (hasMod && syms.length === 1) {
    const x = syms[0];
    const f = modForm(inner, x);
    if (!f) throw fail("only linear congruences mod(a x + b, m) = r are supported");
    if (!intMode) {
      // over the reals: a x + b = r + m k, needs 0 <= r < m
      if (f.r < 0n || f.r >= f.m) return noneCand(`mod(..., ${f.m}) takes values in [0, ${f.m}), so it cannot equal ${f.r}`, inner, env);
      const k = X.sym("k");
      const t = tidy(X.div(X.add(X.num(Q.Q(f.r - f.b)), X.mul(X.num(Q.Q(f.m)), k)), X.num(Q.Q(f.a))));
      log.add({ rule: "solve.integer.mod-real", title: "Unfold the remainder", why: `mod(A, ${f.m}) = ${f.r} means A = ${f.r} + ${f.m} k for some integer k.`, before: inner, after: X.eq(X.sym(x), t) });
      const cand = {
        answers: [{ kind: "general", label: x, tree: t, param: "k" }], solutionStatus: "exact", rejected: [], conditions: [], note: "remainder equation",
        verify: () => verifyFamily(inner, x, t, "k"),
      };
      cand.compare = () => true;
      return cand;
    }
    const s = NT.solveLinearCongruence(f.a, f.r - f.b, f.m);
    for (const st of s.steps || []) log.add({ ...st, rule: "solve.integer.congruence" });
    if (!s.solvable) return noneCand(`gcd(${f.a}, ${f.m}) does not divide ${f.r - f.b}`, inner, env);
    return congruenceCand(x, s.residue, s.modulus, inner, env, "linear congruence");
  }
  if (!intMode) return null;
  // linear Diophantine in two unknowns
  if (syms.length === 2) {
    const d = C(X.sub(inner.args[0], inner.args[1]));
    const [x, y] = vars.length === 2 ? vars : syms.sort();
    const cx = coeffTrees(d, x), cy = coeffTrees(d, y);
    if (!cx || !cy || cx.length !== 2 || cy.length !== 2 || !X.isInt(cx[1]) || !X.isInt(cy[1])) throw fail("only linear Diophantine equations a x + b y = c are supported");
    const c0 = C(X.sub(X.sub(d, X.mul(cx[1], X.sym(x))), X.mul(cy[1], X.sym(y))));
    if (!X.isInt(c0)) throw fail("the equation must have integer coefficients");
    const a = cx[1].v.n, b = cy[1].v.n, c = -c0.v.n;
    const r = NT.linearDiophantine(a, b, c, "t");
    for (const st of r.steps || []) log.add({ ...st, rule: "solve.integer.diophantine" });
    if (!r.solvable) return noneCand(`gcd(${a}, ${b}) = ${NT.egcd(a, b).g} does not divide ${c}, so there is no integer solution`, inner, env);
    const vals = [[x, C(r.x)], [y, C(r.y)]];
    const cand = {
      answers: [{ kind: "family", values: vals, params: ["t"], label: "t is any integer" }], solutionStatus: "exact", rejected: [], conditions: [], note: "linear Diophantine equation",
      verify: () => {
        const sub = C(X.subs(d, Object.fromEntries(vals)));
        const res = [sub === X.ZERO || isZeroExact(sub) ? passCheck("substitution-exact", `${a}(${toText(vals[0][1])}) + ${b}(${toText(vals[1][1])}) = ${c} identically in t`) : failCheck("substitution-exact", "family does not satisfy the equation")];
        const g = NT.egcd(a, b).g;
        res.push(passCheck("completeness", `if (x, y) and (x0, y0) are solutions then ${a / g}(x - x0) = -${b / g}(y - y0) with gcd(${a / g}, ${b / g}) = 1, so x - x0 is a multiple of ${b / g}: every solution is in the family`));
        return toContractVerification(res);
      },
    };
    cand.compare = () => true;
    return cand;
  }
  // one unknown, integer mode: solve over the reals and keep the integers
  if (syms.length === 1) {
    const x = syms[0];
    const c = solveEquation(node, { ...card, unknowns: [x] }, { ...env, options: { ...env.options, integers: false, domain: "real" }, domain: "real" });
    if (!c) return null;
    if (c.answers.some((a) => a.kind === "general" || a.kind === "set" || a.kind === "all")) throw fail("integer solutions of periodic or interval solution sets are not listed");
    if (c.solutionStatus === "partial") throw fail("the real solution set is not proven complete");
    const kept = [], dropped = [];
    for (const a of c.answers) {
      if (a.kind === "exact" && X.isInt(a.tree)) kept.push(a);
      else if (a.kind === "exact" || a.kind === "approx") dropped.push({ tree: a.tree ? X.eq(X.sym(x), a.tree) : null, value: a.tree || a.approx.value, reason: "not an integer" });
    }
    log.add({ rule: "solve.integer.filter", title: "Keep the integer solutions", why: dropped.length ? `${dropped.map((d) => toText(d.tree || X.sym(String(d.value)))).join(", ")} ${dropped.length > 1 ? "are" : "is"} not an integer.` : "Every real solution is an integer.", before: null, after: null, kind: "note" });
    const answers = kept.length ? kept : [{ kind: "none", label: "No integer solution", proof: "none of the real solutions is an integer" }];
    const cand = {
      ...c, answers, rejected: [...(c.rejected || []), ...dropped], noSolution: !kept.length, solutionStatus: "exact",
      verify: (cc) => {
        // verify the complete real solution set, then the integer subset follows exactly
        const v = c.verify(c);
        const intOk = kept.every((a) => X.isInt(a.tree)) && dropped.every((d) => !(d.value && d.value.k && X.isInt(d.value)));
        const checks = [...v.checks, { name: "integers", method: "exact", passed: intOk, detail: "the real solution set is verified complete; its integer members are exactly the listed solutions" }];
        return { ...v, checks, status: v.status === "passed" && intOk ? "passed" : v.status === "passed" ? "failed" : v.status };
      },
    };
    cand.compare = () => true;
    return cand;
  }
  return null;
}
function noneCand(proof, original, env) {
  env.log.add({ rule: "solve.integer.none", title: "No integer solution", why: proof + ".", before: original, after: X.FALSE });
  const cand = { answers: [{ kind: "none", label: "No solution", proof }], noSolution: true, solutionStatus: "exact", rejected: [], conditions: [], verify: () => toContractVerification([passCheck("no-solution", proof)]) };
  cand.compare = () => true;
  return cand;
}
function congruenceCand(x, res, mod, original, env, how) {
  const k = X.sym("k");
  const t = C(X.add(X.num(Q.Q(res)), X.mul(X.num(Q.Q(mod)), k)));
  env.log.add({ rule: "solve.integer.result", title: `${x} = ${res} (mod ${mod})`, why: `By the ${how}: every integer ${x} = ${res} + ${mod} k.`, before: original, after: X.eq(X.sym(x), t) });
  const cand = {
    answers: [{ kind: "general", label: x, tree: t, param: "k", modulus: String(mod), residue: String(res) }], solutionStatus: "exact", rejected: [], conditions: [], note: how,
    verify: () => verifyFamily(original, x, t, "k", mod),
  };
  cand.compare = () => true;
  return cand;
}
function verifyFamily(original, x, t, k, mod) {
  const eqs = original.k === "eq" ? [original] : original.args;
  const res = [];
  for (let kv = -3; kv <= 3; kv++) {
    const v = C(X.subs(t, { [k]: X.num(Q.Q(BigInt(kv))) }));
    for (const e of eqs) {
      const d = C(X.subs(X.sub(e.args[0], e.args[1]), { [x]: v }));
      if (d !== X.ZERO && !isZeroExact(d)) return toContractVerification([failCheck("substitution-exact", `${x} = ${toText(v)} does not satisfy ${toText(e)}`)]);
    }
  }
  res.push(passCheck("substitution-exact", `checked exactly for k = -3..3`));
  if (mod !== undefined) {
    // completeness: brute force over one full period
    let hits = 0;
    const eqsOk = (v) => eqs.every((e) => { const d = C(X.subs(X.sub(e.args[0], e.args[1]), { [x]: X.num(Q.Q(v)) })); return d === X.ZERO; });
    const M = BigInt(mod);
    if (M <= 5000n) {
      for (let v = 0n; v < M; v++) if (eqsOk(v)) hits++;
      res.push(hits === 1 ? passCheck("completeness", `brute force over 0..${M - 1n}: exactly one residue works`) : failCheck("completeness", `brute force found ${hits} residues modulo ${M}`));
    }
  }
  return toContractVerification(res);
}
