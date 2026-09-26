// Quelvra compute worker (module worker).
//
// in : { id, type: "solve" | "preview" | "check-work" | "numeric" | "batch" | "prove-prime", input, options: { mode, domain, digits } }
//      batch: input = [{ input, options }]; each item is solved on its own and reported as
//             { ok: true, result } or { ok: false, error } (the Tools tab asks many small questions at once)
//      prove-prime: input = an integer expression; returns the primality proof and an independent
//             re-check of its certificate (engine/primeproof.js), or a factor when composite
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
    case "batch": {
      progress("loading engine");
      const engine = await loadEngine();
      const items = Array.isArray(input) ? input.slice(0, 400) : [];
      const out = [];
      for (let i = 0; i < items.length; i++) {
        progress(`solving ${i + 1} of ${items.length}`);
        const it = items[i] || {};
        try { out.push({ ok: true, result: await engine.solve(String(it.input ?? ""), { ...options, ...(it.options || {}) }) }); }
        catch (e) { out.push({ ok: false, error: errorPayload(e) }); }
      }
      return out;
    }
    case "prove-prime": return provePrime(String(input ?? ""));
    default: {
      const e = new Error("Unknown request type " + type);
      e.code = "PROTOCOL";
      throw e;
    }
  }
}

// Primality with a certificate. The certificate comes from engine/primeproof.js and is re-checked
// by its independent checker; a composite answer carries a factor that is checked by division.
async function provePrime(src) {
  const [{ parse }, { simplify }, PP, NT] = await Promise.all([
    import("./engine/parse.js"), import("./engine/simplify.js"), import("./engine/primeproof.js"), import("./engine/numtheory.js"),
  ]);
  const t = simplify(parse(src));
  if (t.k !== "num" || t.v.d !== 1n) { const e = new Error("Enter a whole number"); e.code = "UNSUPPORTED"; throw e; }
  const n = t.v.n;
  if (n > 10n ** 400n) { const e = new Error("The number has more than 400 digits"); e.code = "BUDGET"; throw e; }
  const proof = PP.proveprime(n);
  const out = { n: n.toString(), status: proof.status, method: proof.method, certificate: proof.certificate, checked: null, factor: null };
  if (proof.status === "prime") out.checked = PP.checkCertificate(proof.certificate);
  else if (proof.status === "composite" && n > 1n) {
    const q = NT.primality(n);
    let f = q.factor ? BigInt(q.factor) : null;
    if (!f) { const r = NT.factor(n, { budget: 400000 }); if (r.factors && r.factors.length && !(r.factors.length === 1 && r.factors[0][1] === 1n)) f = r.factors[0][0]; }
    if (f && f > 1n && f < n && n % f === 0n) { out.factor = f.toString(); out.checked = true; }
    else out.checked = null; // composite by a Fermat / Miller-Rabin witness; no factor found within budget
    out.witness = q.witness ? String(q.witness) : null;
  }
  return out;
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
