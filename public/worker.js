// Quelvra compute worker (module worker).
//
// in : { id, type: "solve" | "preview" | "check-work" | "numeric", input, options: { mode, domain, digits } }
// out: { id, type: "progress", stage }
//      { id, type: "result", result }            trees serialised by bridge-shared.serializeResult
//      { id, type: "error", error: { code, message, pos, hint } }
//
// The engine is loaded lazily so a preview never waits for (or breaks because of) the solver.
// Heavy jobs are cancelled by the page terminating this worker; there is no cooperative abort.

import { parseDetailed, unknownWords } from "./engine/parse.js";
import { translate } from "./engine/language.js";
import { serializeResult, errorPayload } from "./bridge-shared.js";

let enginePromise = null;
let researchMod = null;
const loadEngine = () => (enginePromise ||= import("./engine/quelvra.js"));

const post = (msg) => self.postMessage(msg);
const now = () => performance.now();

async function handle(msg) {
  const { id, type } = msg;
  const input = msg.input;
  const options = msg.options || {};
  const progress = (stage) => post({ id, type: "progress", stage });
  switch (type) {
    case "preview": {
      const t0 = now();
      let src = String(input ?? "");
      // research requests ("goldbach up to 10^6", "riemann hypothesis") are named, not parsed
      try {
        researchMod ||= import("./engine/strategies/research.js");
        const rec = (await researchMod).recogniseResearch(src);
        if (rec) return { tree: null, text: rec.label, warnings: [], ms: now() - t0 };
      } catch (_) { /* engine not available: fall through to the parser */ }
      // read words the same way solve() does, so "factor x^4 - 1" previews as factor(x^4 - 1)
      try { const t = translate(src); if (t && t.ok && t.math) src = t.math; else {
        const words = unknownWords(src);
        if (words.length >= 2 || words.some((w) => w.length >= 4)) {
          const e = new Error(`Quelvra does not understand "${words[0]}"`);
          e.code = "UNKNOWN_WORDS"; e.pos = src.indexOf(words[0]);
          throw e;
        }
      } } catch (e) { if (e && e.code === "UNKNOWN_WORDS") throw e; }
      const { node, warnings } = parseDetailed(src);
      return { tree: node, warnings, ms: now() - t0 };
    }
    case "solve": {
      progress("loading engine");
      const engine = await loadEngine();
      progress("solving");
      const result = await engine.solve(String(input ?? ""), { ...options, onProgress: progress });
      progress("preparing result");
      return result;
    }
    case "check-work": {
      progress("loading engine");
      const engine = await loadEngine();
      if (typeof engine.checkWork !== "function") {
        const e = new Error("This engine build has no work checker");
        e.code = "UNSUPPORTED";
        throw e;
      }
      progress("checking lines");
      const lines = Array.isArray(input) ? input.map(String) : String(input ?? "").split("\n");
      return await engine.checkWork(lines, { ...options, onProgress: progress });
    }
    case "numeric": {
      progress("loading engine");
      const engine = await loadEngine();
      if (typeof engine.numeric === "function") return await engine.numeric(String(input ?? ""), options);
      progress("solving");
      return await engine.solve(String(input ?? ""), { ...options, mode: "numeric", onProgress: progress });
    }
    default: {
      const e = new Error("Unknown request type " + type);
      e.code = "PROTOCOL";
      throw e;
    }
  }
}

self.onmessage = async (ev) => {
  const msg = ev.data || {};
  try {
    const raw = await handle(msg);
    post({ id: msg.id, type: "result", result: serializeResult(raw) });
  } catch (e) {
    post({ id: msg.id, type: "error", error: errorPayload(e) });
  }
};
