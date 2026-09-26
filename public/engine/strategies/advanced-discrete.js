// Advanced discrete mathematics (call forms; plain-English phrasings are translated to these by
// ../discrete/lang.js):
//
//   sequences   rsolve genfunc seriescoeff findsequence
//   graphs      graphdegrees graphcomponents shortestpath minspantree countspanningtrees isbipartite
//               eulerpath hamiltonpath chromaticnumber chromaticpoly isplanar maxflow toposort isisomorphic
//   logic       truthtable istautology issatisfiable logicequiv cnf dnf minsop validargument
//   sets        setcalc divcount unionsize relprops funcprops fcompose
//   algebra     perminfo permcompose elementorder unitgroup cyclicgroup abeliangroups gfcalc factormod
//               isirreducible gaussgcd gaussfactor quotientring
//   LP / games  linprog intprog matrixgame nashequilibria
//   crypto      rsakeys rsadecrypt rsacrt modpow modinverse dlog diffiehellman
//   topology    homology eulerchar
//   proofs      provedivisible proveidentity provesum provebound provealwaysprime provefinite proveequiv proofrequest
//
// Every handler returns { answers, steps, checks, solutionStatus?, note? } where checks() runs an
// INDEPENDENT verification (certificate check, second algorithm, brute force or exact identity).
// The answer is shown only when at least one check ran and every check passed; otherwise it is
// withheld (never guessed).

import { register, toContractVerification, unsupported } from "../orchestrate.js";
import { ADV_DISCRETE_COMMANDS } from "../discrete/names.js";
import { GRAPH_HANDLERS } from "../discrete/graph.js";
import { SEQ_HANDLERS } from "../discrete/sequences.js";
import { LOGIC_HANDLERS } from "../discrete/logic.js";
import { SET_HANDLERS } from "../discrete/sets.js";
import { ALGEBRA_HANDLERS } from "../discrete/algebra.js";
import { LP_HANDLERS } from "../discrete/lp.js";
import { CRYPTO_HANDLERS } from "../discrete/crypto.js";
import { TOPOLOGY_HANDLERS } from "../discrete/topology.js";
import { PROOF_HANDLERS } from "../discrete/proof.js";

export const HANDLERS = { ...SEQ_HANDLERS, ...GRAPH_HANDLERS, ...LOGIC_HANDLERS, ...SET_HANDLERS, ...ALGEBRA_HANDLERS, ...LP_HANDLERS, ...CRYPTO_HANDLERS, ...TOPOLOGY_HANDLERS, ...PROOF_HANDLERS };

const PASSTHROUGH = ["UNSUPPORTED", "TIMEOUT", "BUDGET"];

function verifyWith(checksFn) {
  return () => {
    let cs;
    try { cs = checksFn(); } catch (e) {
      if (e && e.code === "TIMEOUT") throw e;
      return toContractVerification([{ status: "failed", checks: [{ kind: "verification", ok: false, detail: `the independent check could not be completed (${e && e.message}); the answer is withheld` }] }]);
    }
    cs = (cs || []).filter(Boolean);
    if (!cs.length) return toContractVerification([{ status: "failed", checks: [{ kind: "policy", ok: false, detail: "no independent check was available, so the answer is withheld" }] }]);
    const ok = cs.every((c) => c.ok);
    return toContractVerification([{ status: ok ? "verified-exact" : "failed", checks: cs }]);
  };
}

export function runDiscrete(name, node, env) {
  const h = HANDLERS[name];
  if (!h) throw unsupported(`${name} is not available`);
  let r;
  try { r = h(node.args || [], env, node); } catch (e) {
    if (e && PASSTHROUGH.includes(e.code)) throw e;
    if (e instanceof RangeError || e instanceof TypeError) throw unsupported(`${name} could not handle this input (${e.message})`);
    throw e;
  }
  if (!r) return null;
  return {
    answers: r.answers, steps: r.steps || [], solutionStatus: r.solutionStatus || "exact", note: r.note || "",
    conditions: r.conditions || [], extra: r.extra || null,
    verify: verifyWith(r.checks || (() => [])),
  };
}

for (const name of ADV_DISCRETE_COMMANDS) {
  register({
    id: `adv.${name}`, kinds: ["command"], priority: 3,
    applies: (card) => card.command === name,
    run: (node, card, env) => runDiscrete(name, node, env),
  });
}
