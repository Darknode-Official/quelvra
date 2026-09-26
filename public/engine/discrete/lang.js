// Plain-English and friendly call-form recognition for the advanced discrete commands.
//
// translateAdvancedDiscrete(text) returns a language.translate()-style result whose `math` is a
// canonical call form (see names.js), or null when the text is not one of these requests. It
// never throws: any internal error means "not recognised here", and the ordinary translator runs.
//
// The area recognisers live in lang-*.js; this file holds the shared text helpers and the
// dispatcher. Recognisers are deliberately conservative: each one needs an unambiguous keyword
// (a command name, "graph", "truth table", "GF(", "RSA", "homology", ...) before it claims input,
// so ordinary algebra and calculus inputs are never captured.

import { parseDetailed } from "../parse.js";
import { normalise } from "./lang-util.js";
import { recogniseGraph } from "./lang-graph.js";
import { recogniseLogic } from "./lang-logic.js";
import { recogniseSets } from "./lang-sets.js";
import { recogniseAlgebra } from "./lang-algebra.js";
import { recogniseLP } from "./lang-lp.js";
import { recogniseCrypto } from "./lang-crypto.js";
import { recogniseSeq } from "./lang-seq.js";
import { recogniseTopology } from "./lang-topology.js";
import { recogniseProof } from "./lang-proof.js";

const RECOGNISERS = [recogniseProof, recogniseGraph, recogniseLogic, recogniseSets, recogniseAlgebra, recogniseLP, recogniseCrypto, recogniseSeq, recogniseTopology];

export function translateAdvancedDiscrete(input) {
  try {
    let text = normalise(input);
    // "edges A-B 4, B-C 2": a bare number after an edge is its weight (A-B:4)
    if (text && /\bgraph|\bedges?\b/i.test(text)) text = text.replace(/\b(\w+)\s*(->|-)\s*(\w+)\s+(\d+(?:\.\d+)?)(?=\s*(?:,|;|$|\band\b))/g, "$1$2$3:$4");
    if (!text || text.length > 4000) return null;
    for (const r of RECOGNISERS) {
      const hit = r(text);
      if (!hit) continue;
      const math = typeof hit === "string" ? hit : hit.math;
      try { parseDetailed(math); } catch (_) { continue; }
      return {
        ok: true, math, goal: null, variable: undefined, pattern: "adv-discrete", confidence: 0.95,
        interpretation: (hit && hit.interpretation) || math, notes: (hit && hit.notes) || [],
      };
    }
  } catch (_) { /* not recognised here */ }
  return null;
}

