// Integration strategies.
//
//   integrate.symbolic  (priority 10)  antiderivatives, definite and improper integrals: exact trees,
//                                      proven divergence, or a numeric value when no exact method applies
//   integrate.numeric   (priority 60, crossCheck) independent quadrature (numeric.js) for definite
//                                      integrals; the orchestrator compares it with the exact value
//
// Every antiderivative is verified by differentiation (verify.js when it can evaluate the result, the
// integrator's own real-domain derivative check otherwise); every definite value is cross-checked by
// quadrature before it is reported.

import * as X from "../expr.js";
import { toText } from "../print.js";
import { diff } from "../calc/diff.js";
import { verifyAntiderivative } from "../verify.js";
import * as NUM from "../numeric.js";
import { register, toContractVerification, unsupported } from "../orchestrate.js";
import { integrate } from "../calc/integrate.js";
import { definiteIntegral, independentQuad } from "../calc/int-definite.js";
import { checkAntiderivative, usesSpecial, evalD, SPECIAL } from "../calc/int-util.js";

const now = () => (typeof performance !== "undefined" ? performance.now() : Date.now());
const hasSpecialFn = (u) => (u.k === "fn" && SPECIAL.has(u.name)) || u.args.some(hasSpecialFn);

function approxRecord(tree, value, digits) {
  if (!hasSpecialFn(tree)) {
    try {
      const r = NUM.N(tree, digits);
      if (r && r.value && r.converged !== false) return r;
    } catch (e) { if (!e || !e.code) throw e; }
  }
  if (!Number.isFinite(value)) return null;
  // double-precision evaluation of the special functions: about 12 correct digits
  return { value: String(+value.toPrecision(12)), digits: 12, requested: digits, errorBound: `${(Math.abs(value) * 1e-11 + 1e-14).toExponential(1)}`, method: "double-precision evaluation", iterations: 0, converged: true };
}

const V = (status, checks) => toContractVerification([{ status, checks }]);

function approxValueOf(c) {
  const a = (c.answers || []).find((z) => z.kind === "approx" && z.approx);
  return a ? Number(a.approx.value) : NaN;
}

register({
  id: "integrate.symbolic", kinds: ["integral"], priority: 10,
  run(node, card, env) {
    const [u, x, lo, hi] = node.args;
    const remaining = Math.max(500, env.deadline - now() - 200);
    if (node.args.length !== 4) {
      // ---------------- antiderivative
      let r;
      try {
        r = integrate(u, x, { steps: env.log, timeLimit: Math.min(remaining, 7000) });
      } catch (e) {
        if (e && e.code === "NONELEMENTARY") {
          return { answers: [{ kind: "none", label: "No elementary antiderivative", reason: e.message }], solutionStatus: "exact", note: "proved non-elementary",
            verify: () => ({ status: "not-applicable", checks: [] }) };
        }
        if (e && (e.code === "UNSUPPORTED" || e.code === "BUDGET" || e.code === "TIMEOUT")) throw unsupported(e.code === "UNSUPPORTED" ? e.message : "Quelvra could not find a verified antiderivative within its resource limits.");
        throw e;
      }
      const F = r.F;
      const notes = [...r.conditions];
      if (r.special) notes.push("The antiderivative uses a special function because this integral has no elementary antiderivative.");
      return {
        answers: [{ kind: "exact", tree: F, constant: true }], solutionStatus: "exact", note: notes.join(" "), extra: { method: r.method, notes, special: !!r.special },
        graph: X.freeSymbols(u).size <= 1 && !hasSpecialFn(F) ? { exprs: [u, F], marks: [] } : null,
        verify: () => {
          if (!usesSpecial(F)) {
            const v = verifyAntiderivative(F, u, x.name, { diffFn: (a, b) => diff(a, b) });
            if (v.status !== "inconclusive") return toContractVerification([v]);
          }
          const c = checkAntiderivative(F, u, x, {});
          return V(c.ok === true ? "verified-numeric" : c.ok === false ? "failed" : "inconclusive",
            [{ kind: "derivative", method: "numeric", ok: c.ok !== false, detail: c.ok === true ? `d/d${x.name} of the answer matches the integrand at ${c.good} points on the real domain (special functions evaluated independently)` : String(c.detail) }]);
        },
      };
    }
    // ---------------- definite / improper
    let r;
    try {
      r = definiteIntegral(u, x, lo, hi, { steps: env.log, pv: !!(env.options && env.options.pv), digits: Math.min(env.digits || 15, 14), timeLimit: Math.min(remaining, 7000) });
    } catch (e) {
      if (e && e.code === "NOTREAL") return { answers: [{ kind: "none", label: "The integral is not defined over the reals", reason: e.message }], solutionStatus: "exact", verify: () => ({ status: "not-applicable", checks: [] }) };
      if (e && (e.code === "UNSUPPORTED" || e.code === "BUDGET" || e.code === "TIMEOUT")) throw unsupported(e.code === "UNSUPPORTED" ? e.message : "Quelvra could not evaluate this integral within its resource limits.");
      throw e;
    }
    if (r.status === "diverges") {
      return { answers: [{ kind: "none", label: "The integral diverges", reason: r.reason }], solutionStatus: "exact", note: "divergent",
        verify: () => V("verified-numeric", (r.checks || []).map((d) => ({ kind: "piece-check", method: "numeric", ok: true, detail: d }))) };
    }
    if (r.status === "approx") {
      return { answers: [{ kind: "approx", approx: r.record }], solutionStatus: "approximate", note: r.reason, extra: { reason: r.reason, nonelementary: r.nonelementary || null },
        verify: () => {
          if (r.singleMethod) return V("inconclusive", [{ kind: "quadrature", method: "numeric", ok: null, detail: "only one quadrature method converged; no independent confirmation" }]);
          const q = independentQuad(u, x, lo, hi);
          if (!q.ok) return V("inconclusive", [{ kind: "quadrature", method: "numeric", ok: null, detail: "the independent Gauss-Kronrod quadrature did not converge" }]);
          const eb = Number(r.record && r.record.errorBound);
          const tol = Math.max(10 * (Number.isFinite(eb) ? eb : 0), 10 * q.err, 1e-9 * Math.max(1, Math.abs(q.value)));
          const good = Math.abs(q.value - r.value) <= tol;
          return V(good ? "verified-numeric" : "failed", [{ kind: "quadrature", method: "numeric", ok: good, detail: `independent adaptive Gauss-Kronrod quadrature gives ${q.value.toPrecision(13)} (${good ? "agrees" : "DISAGREES"})` }]);
        },
        compare: (other) => { const o = approxValueOf(other); return !Number.isFinite(o) || Math.abs(o - r.value) <= 1e-8 * Math.max(1, Math.abs(o)); } };
    }
    const answers = [{ kind: "exact", tree: r.value }];
    const rec = X.freeSymbols(r.value).size === 0 ? approxRecord(r.value, r.approx, env.digits || 15) : null;
    if (rec && !(X.isNum(r.value) && r.value.v.d === 1n)) answers.push({ kind: "approx", approx: rec });
    const notes = [...(r.conditions || [])];
    if (r.pv) notes.push("Cauchy principal value");
    return {
      answers, solutionStatus: "exact", note: notes.join(" "), extra: { method: r.method, antiderivative: r.F, notes, pv: !!r.pv },
      verify: () => {
        if (!Number.isFinite(r.approx)) return V("verified-exact", [{ kind: "ftc", method: "exact", ok: true, detail: (r.checks || []).join("; ") }]);
        return V("verified-numeric", (r.checks || []).map((d) => ({ kind: "quadrature", method: "numeric", ok: true, detail: d })));
      },
      compare: (other) => {
        const o = approxValueOf(other);
        if (!Number.isFinite(o) || !Number.isFinite(r.approx)) return true;
        return Math.abs(o - r.approx) <= 1e-8 * Math.max(1, Math.abs(r.approx));
      },
    };
  },
});

register({
  id: "integrate.numeric", kinds: ["integral"], families: ["definite-integral", "improper-integral"], priority: 60, crossCheck: true,
  run(node, card, env) {
    if (node.args.length !== 4) return null;
    const [u, x, lo, hi] = node.args;
    if ([...X.freeSymbols(u)].some((n) => n !== x.name) || X.freeSymbols(lo).size || X.freeSymbols(hi).size) return null;
    if (hasSpecialFn(u)) return null;
    let rec;
    try { rec = NUM.integrate(u, x.name, lo, hi, { digits: Math.min(env.digits || 15, 14) }); } catch (e) {
      if (e && e.code) throw unsupported(e.message);
      throw e;
    }
    if (!rec || rec.value === "undefined" || !rec.converged) throw unsupported("numerical quadrature did not converge");
    void evalD; void toText;
    return { answers: [{ kind: "approx", approx: rec }], solutionStatus: "approximate", verify: () => ({ status: "not-applicable", checks: [] }) };
  },
});
