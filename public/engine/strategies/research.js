// Quelvra strategy: the open problems lab.
//
// Honesty contract: Quelvra never claims a proof of an open problem. It offers
//   (a) exact, complete results where the question is finite (Kaprekar's routine for a digit count,
//       a single Collatz trajectory, a Goldbach decomposition of one number),
//   (b) verified computational evidence up to a stated bound, labelled "evidence, not a proof",
//   (c) accurate expository cards.
//
// Exports:
//   recogniseResearch(text) -> { command, args, label } | null   (English / command recognition)
//   runResearch(command, args, opts) -> Solver-result-like object (CONTRACT.md) with kind "research"
//   RESEARCH_FUNCTIONS: function names the strategy handles when they arrive as parsed calls, e.g. collatz(27)
// and registers one orchestrator strategy (id "research", kinds ["command"]).

import * as X from "../expr.js";
import { simplify } from "../simplify.js";
import * as T from "../numtheory.js";
import { register } from "../orchestrate.js";
import { Budget, parseIntText, fmtInt, now } from "../research/budget.js";
import { kaprekar, kaprekarStep, formatFixed } from "../research/kaprekar.js";
import { collatz, collatzVerify } from "../research/collatz.js";
import { goldbach, goldbachVerify, primeStats, isPrimeTrial, isPrimeMR2, KNOWN_PI, KNOWN_PI2 } from "../research/primes.js";
import { zetaZeros, zeta, zetaEM, Z, ZEM, ZRS, RS_THRESHOLD, KNOWN_ZEROS } from "../research/zeta.js";
import { eulerBricks, eulerBricksBrute, isqrtBig } from "../research/bricks.js";
import { movingSofa, hammersleyAreaNumeric } from "../research/sofa.js";
import { CARDS, cardIdFor, honestNote } from "../research/cards.js";

export { CARDS };
export const DEFAULTS = { kaprekar: 4, collatzVerify: 1000000, goldbachVerify: 1000000, twinPrimes: 1000000, primeGaps: 1000000, zetaZeros: 1000, eulerBricks: 10000 };
const EVIDENCE = "Evidence, not a proof.";

// ------------------------------------------------------------------ recognition
const NUM = String.raw`(\(?\d[\d,_]*(?:\.\d+)?(?:e\+?\d+)?(?:\s*(?:\^|\*\*|\*|x|\+|-)\s*\(?\d+(?:\.\d+)?(?:e\+?\d+)?\)?)*(?:\s*(?:thousand|million|billion|trillion))?)`;
const UPTO = String.raw`(?:up to|upto|to|below|under|until|through|less than|<=|<|till|for (?:all )?(?:n|numbers|even numbers|values)?\s*(?:up to|<=|below|<)?)`;
const num = (s) => {
  let t = String(s).replace(/\s+/g, " ").trim();
  const bal = (x) => (x.match(/\(/g) || []).length - (x.match(/\)/g) || []).length;
  while (bal(t) < 0 && t.endsWith(")")) t = t.slice(0, -1).trim();
  while (bal(t) > 0 && t.startsWith("(")) t = t.slice(1).trim();
  return parseIntText(t);
};
const PROOF_INTENT = /\b(prove|proof|disprove|solve|solving|resolve|settle|crack|answer to)\b/;

export function recogniseResearch(text) {
  let t = String(text || "").toLowerCase().normalize("NFKD").replace(/[̀-ͯ]/g, "")
    .replace(/[?!.]+$/, "").replace(/\s+/g, " ").trim()
    .replace(/^(?:please |can you |could you |quelvra,? |hey,? |now |ok,? )+/, "").replace(/ please$/, "").trim();
  if (!t) return null;
  // a plain equation, inequality or formula ("x^3 - 3x + 1 = 0") is ordinary math unless it
  // names a research topic in words
  if (/[=<>≤≥^]|[a-z]\s*\(|\d\s*[a-z]/.test(t) && !cardIdFor(t) && !/zeta|kaprekar|collatz|goldbach|twin|gap|brick|sofa|hailstone|syracuse/.test(t)) return null;
  const R = (re) => t.match(new RegExp(re.replace(/NUM/g, NUM).replace(/UPTO/g, UPTO)));

  // 1. asked to prove / solve an open problem: honest card
  const idAny = cardIdFor(t);
  if (idAny && CARDS[idAny].open && PROOF_INTENT.test(t) && !/\b(?:verify|check|count|compute|list|find|zeros?)\b.*\d/.test(t))
    return { command: "card", args: { id: idAny, askedForProof: true }, label: `${CARDS[idAny].title} (asked for a proof)` };

  let m;
  // 2. Kaprekar
  if ((m = R(String.raw`^(?:run |compute |classify |solve |show )?(?:the )?kaprekar(?:'s)?(?: routine| constant| process| map| problem)?(?: (?:for|with|on))?\s*\(?\s*(\d+)\s*\)?(?:[\s-]*digits?(?: numbers?)?)?(?:\s*,?\s*(?:in )?base\s*(\d+))?$`)))
    return { command: "kaprekar", args: { digits: Number(m[1]), base: m[2] ? Number(m[2]) : 10 }, label: `Kaprekar routine, ${m[1]} digits${m[2] ? `, base ${m[2]}` : ""}` };
  if ((m = R(String.raw`^kaprekar(?:'s)?(?: routine| constant| process)? (?:for )?(\d+)[\s-]*digit numbers?(?: in base (\d+))?$`)))
    return { command: "kaprekar", args: { digits: Number(m[1]), base: m[2] ? Number(m[2]) : 10 }, label: `Kaprekar routine, ${m[1]} digits` };
  if (/^(?:the )?kaprekar(?:'s)?(?: routine| constant| process)?$|^6174$|^what is (?:special about )?6174$/.test(t))
    return { command: "kaprekar", args: { digits: 4, base: 10 }, label: "Kaprekar routine, 4 digits (6174)" };

  // 3. Collatz
  if ((m = R(String.raw`^(?:verify|check|test|confirm|run)\s+(?:the\s+)?(?:collatz|3n\s*\+\s*1|hailstone)(?:\s+conjecture|\s+problem)?\s*(?:UPTO\s*)?(?:n\s*=\s*)?NUM$`)) ||
      (m = R(String.raw`^(?:collatz|3n\s*\+\s*1)(?:\s+conjecture)?\s+(?:verify|verification|check)\s*(?:UPTO\s*)?NUM$`)) ||
      (m = R(String.raw`^(?:collatz|3n\s*\+\s*1)(?:\s+conjecture)?\s+UPTO\s*NUM$`))) {
    const N = num(m[1]); if (N !== null) return { command: "collatzVerify", args: { N }, label: `Verify the Collatz conjecture for all n <= ${fmtInt(N)}` };
  }
  if (/^(?:verify|check|test)\s+(?:the\s+)?(?:collatz|3n\s*\+\s*1)(?:\s+conjecture)?$/.test(t))
    return { command: "collatzVerify", args: { N: BigInt(DEFAULTS.collatzVerify) }, label: `Verify the Collatz conjecture for all n <= ${fmtInt(DEFAULTS.collatzVerify)}` };
  if ((m = R(String.raw`^(?:the\s+)?(?:collatz|hailstone|3n\s*\+\s*1|syracuse)(?:\s+(?:sequence|trajectory|orbit|path|steps|chain|map))?\s*(?:of|for|from|starting (?:at|from)|at)?\s*\(?\s*(?:n\s*=\s*)?NUM\s*\)?$`))) {
    const n = num(m[1]); if (n !== null) return { command: "collatz", args: { n }, label: `Collatz trajectory of ${n}` };
  }

  // 4. Goldbach
  if ((m = R(String.raw`^(?:verify|check|test|confirm|run)\s+(?:the\s+)?goldbach(?:'s)?(?:\s+conjecture)?\s*(?:UPTO\s*)?(?:n\s*=\s*)?NUM$`)) ||
      (m = R(String.raw`^goldbach(?:'s)?(?:\s+conjecture)?\s+UPTO\s*NUM$`)) || (m = R(String.raw`^goldbach(?:\s+conjecture)?\s+(?:verify|verification|check)\s*(?:UPTO\s*)?NUM$`))) {
    const N = num(m[1]); if (N !== null) return { command: "goldbachVerify", args: { N }, label: `Verify the Goldbach conjecture for every even n <= ${fmtInt(N)}` };
  }
  if (/^(?:verify|check|test)\s+(?:the\s+)?goldbach(?:'s)?(?:\s+conjecture)?$/.test(t))
    return { command: "goldbachVerify", args: { N: BigInt(DEFAULTS.goldbachVerify) }, label: `Verify the Goldbach conjecture for every even n <= ${fmtInt(DEFAULTS.goldbachVerify)}` };
  if ((m = R(String.raw`^goldbach(?:'s)?(?:\s+(?:decomposition|partition|pair|split|sum))?\s*(?:of|for)?\s*\(?\s*NUM\s*\)?$`)) ||
      (m = R(String.raw`^(?:write|express|decompose|split)\s+NUM\s+(?:as|into)\s+(?:a\s+)?sum of two primes$`)) ||
      (m = R(String.raw`^is\s+NUM\s+(?:a\s+)?sum of two primes$`))) {
    const n = num(m[1]); if (n !== null) return { command: "goldbach", args: { n }, label: `Goldbach decomposition of ${n}` };
  }

  // 5. twin primes, prime gaps
  if ((m = R(String.raw`^(?:count |find |list |how many |number of |compute )?(?:the )?twin[\s-]*primes?(?:\s+pairs)?(?: are there)?\s*(?:UPTO\s*)?NUM$`)) ||
      (m = R(String.raw`^(?:count |how many )?twin[\s-]*primes?(?: are there)? (?:UPTO|in) NUM$`))) {
    const N = num(m[1]); if (N !== null) return { command: "twinPrimes", args: { N }, label: `Twin primes up to ${fmtInt(N)}` };
  }
  if ((m = R(String.raw`^(?:maximal |record |largest )?prime gaps?(?:\s+records?)?\s*(?:UPTO\s*)?NUM$`))) {
    const N = num(m[1]); if (N !== null) return { command: "primeGaps", args: { N }, label: `Prime gap records up to ${fmtInt(N)}` };
  }

  // 6. zeta zeros and zeta values
  if ((m = R(String.raw`^(?:find |compute |list |locate |verify |check |count )?(?:the )?(?:first\s+)?(\d+)\s+(?:nontrivial\s+|non-trivial\s+)?(?:riemann\s+)?(?:zeta\s+)?zeros(?: of (?:the )?(?:riemann )?zeta(?: function)?)?$`)))
    return { command: "zetaZeros", args: { count: Number(m[1]) }, label: `First ${m[1]} nontrivial zeros of zeta` };
  if ((m = R(String.raw`^(?:find |compute |list |locate |verify |check |count )?(?:the )?(?:nontrivial |non-trivial )?(?:riemann(?:'s)? |riemann zeta |zeta )?zeros(?: of (?:the )?(?:riemann )?zeta(?: function)?)?(?: on the critical line)?\s*(?:(?:with )?(?:imaginary part |height |im(?:\s*s)? |t )?UPTO\s*)?(?:t\s*=\s*|height\s+)?NUM$`)) ||
      (m = R(String.raw`^(?:verify|check|test)\s+(?:the\s+)?riemann hypothesis\s+(?:UPTO|up to height)\s*(?:t\s*=\s*|height\s+)?NUM$`))) {
    const T2 = num(m[1]); if (T2 !== null && /zero|riemann/.test(t)) return { command: "zetaZeros", args: { T: Number(T2) }, label: `Nontrivial zeros of zeta with 0 < Im s < ${T2}` };
  }
  if (/^(?:the )?(?:riemann )?zeta zeros$|^(?:nontrivial )?zeros of (?:the )?(?:riemann )?zeta(?: function)?$|^(?:verify|check|test) (?:the )?riemann hypothesis$/.test(t))
    return { command: "zetaZeros", args: { T: DEFAULTS.zetaZeros }, label: `Nontrivial zeros of zeta with 0 < Im s < ${DEFAULTS.zetaZeros}` };
  if ((m = t.match(/^(?:riemann )?zeta\s*(?:\(\s*(.+?)\s*\)|of\s+(.+)|at\s+(.+))$/))) {
    const s = parseComplex(m[1] || m[2] || m[3]);
    if (s) return { command: "zeta", args: { re: s[0], im: s[1] }, label: `zeta(${fmtComplex(s)})` };
  }

  // 7. Euler bricks / perfect cuboid
  if ((m = R(String.raw`^(?:find |list |search |search for |enumerate |count )?(?:all )?(?:euler bricks?|perfect cuboids?|perfect euler bricks?)(?:\s+with)?(?:\s+(?:largest |max(?:imum)? )?(?:edges?|sides?))?\s*(?:UPTO\s*)?NUM$`))) {
    const L = num(m[1]); if (L !== null) return { command: "eulerBricks", args: { maxEdge: L }, label: `Euler bricks with largest edge <= ${fmtInt(L)}` };
  }
  if (/^(?:find |search for |list )?(?:a |all |the )?(?:euler bricks?|perfect cuboids?|perfect euler bricks?|perfect box(?:es)?)(?: problem)?$|^is there a perfect cuboid$/.test(t))
    return { command: "eulerBricks", args: { maxEdge: BigInt(DEFAULTS.eulerBricks) }, label: `Euler bricks with largest edge <= ${fmtInt(DEFAULTS.eulerBricks)} (perfect cuboid search)` };

  // 8. moving sofa
  if (/\bsofa\b/.test(t)) return { command: "sofa", args: {}, label: "Moving sofa problem" };

  // 9. twin primes / goldbach / collatz bare names with no number: card (plus computation offered)
  const id = idAny;
  if (id) {
    if (id === "kaprekar") return { command: "kaprekar", args: { digits: 4, base: 10 }, label: "Kaprekar routine, 4 digits (6174)" };
    // bare names only: avoid hijacking longer math sentences that merely mention a word
    const words = t.split(" ").length;
    if (words <= 8 || /^(?:what is|what's|explain|tell me about|describe|status of|is the)\b/.test(t) || PROOF_INTENT.test(t))
      return { command: "card", args: { id, askedForProof: PROOF_INTENT.test(t) && CARDS[id].open }, label: CARDS[id].title };
  }
  return null;
}
function parseComplex(src) {
  const s = String(src).replace(/\s+/g, "").replace(/\*i$/, "i").replace(/(\d)\*?i/g, "$1i");
  let m = s.match(/^([+-]?\d*\.?\d+(?:e[+-]?\d+)?)$/);
  if (m) return [Number(m[1]), 0];
  m = s.match(/^([+-]?\d*\.?\d+(?:e[+-]?\d+)?)?([+-])(\d*\.?\d*(?:e[+-]?\d+)?)i$/);
  if (m) return [m[1] ? Number(m[1]) : 0, (m[2] === "-" ? -1 : 1) * (m[3] === "" ? 1 : Number(m[3]))];
  m = s.match(/^([+-]?\d*\.?\d+(?:e[+-]?\d+)?)i$/);
  if (m) return [0, Number(m[1])];
  return null;
}
const fmtComplex = ([a, b]) => (b === 0 ? String(a) : a === 0 ? `${b}i` : `${a} ${b < 0 ? "-" : "+"} ${Math.abs(b)}i`);

// ------------------------------------------------------------------ result assembly
const check = (name, passed, detail, method = "independent") => ({ name, method, passed: !!passed, detail });
function verification(checks) {
  const failed = checks.some((c) => !c.passed);
  return { status: !checks.length ? "not-applicable" : failed ? "failed" : "passed", level: "exact", checks };
}
const note = (rule, title, why) => ({ rule: `research.${rule}`, title, why, before: null, after: null, conditions: [], sub: [], kind: "note", check: null });
const intTree = (v) => { try { return X.num(BigInt(v)); } catch (_) { return null; } };
function mkResult({ command, family, label, answers, solutionStatus, checks, steps, extra, t0 }) {
  return {
    ok: solutionStatus !== "unsupported", input: { text: label, tree: null, warnings: [] }, recognition: { source: "research", confidence: 1 },
    classification: { kind: "research", family, label, command, goal: "research", unknowns: [] },
    answers, solutionStatus, verification: verification(checks || []), steps: steps || [], conditions: [], rejected: [],
    attempts: [{ strategy: "research", status: "ok", reason: "", ms: now() - t0 }], graph: null, method: "research",
    extra: extra || null, ms: now() - t0,
  };
}
function failResult(command, label, e, t0) {
  const reason = e && (e.code === "TIMEOUT" || e.code === "BUDGET") ? `${e.message} Nothing is reported beyond what was completed.` : e && e.message ? e.message : String(e);
  return {
    ok: false, input: { text: label, tree: null, warnings: [] }, recognition: { source: "research", confidence: 1 },
    classification: { kind: "research", family: command, label, command }, answers: [{ kind: "none", label: reason }],
    solutionStatus: e && (e.code === "UNSUPPORTED" || e.code === "DOMAIN") ? "unsupported" : "unsolved",
    verification: { status: "not-applicable", checks: [] }, steps: [], conditions: [], rejected: [],
    attempts: [{ strategy: "research", status: "failed", reason, ms: now() - t0 }], graph: null, error: { message: reason, code: e && e.code }, ms: now() - t0,
  };
}
// deterministic PRNG for spot checks
function prng(seed = 20260925) { let a = seed >>> 0; return () => { a = (a + 0x6d2b79f5) >>> 0; let x = a; x = Math.imul(x ^ (x >>> 15), x | 1); x ^= x + Math.imul(x ^ (x >>> 7), x | 61); return ((x ^ (x >>> 14)) >>> 0) / 4294967296; }; }

// ------------------------------------------------------------------ commands
const RUN = {
  kaprekar(args, budget) {
    const d = Number(args.digits ?? DEFAULTS.kaprekar), b = Number(args.base ?? 10);
    const r = kaprekar(d, b, { budget });
    const fp = r.fixedPoints.map((x) => formatFixed(x, d, b));
    const cyc = r.cycles.map((c) => c.membersText.join(" -> "));
    const answers = [
      { kind: "exact", label: "Fixed points", text: fp.length ? fp.join(", ") : "none", tree: fp.length === 1 && b === 10 ? intTree(r.fixedPoints[0]) : undefined },
      { kind: "exact", label: "Cycles (length > 1)", text: cyc.length ? cyc.join("; ") : "none" },
      { kind: "exact", label: "Maximum number of steps to reach a fixed point or cycle", text: String(r.maxSteps), tree: intTree(r.maxSteps) },
      { kind: "info", label: "Status", text: `Complete classification for ${d}-digit strings in base ${b}: proved by exhaustive computation over all ${fmtInt(r.multisets)} digit multisets (every one of the ${fmtInt(r.totalAll)} strings is covered).` },
    ];
    const rows = r.attractors.map((a) => ({ type: a.type, members: a.membersText.join(" -> "), basinProper: String(a.basinProper), basinAll: String(a.basinAll), maxSteps: a.maxSteps }));
    const steps = [
      note("kaprekar.multisets", "Reduce to digit multisets", `K(x) depends only on the multiset of digits of x, so the ${b}^${d} strings collapse to ${fmtInt(r.multisets)} multisets.`),
      note("kaprekar.graph", "Build the functional graph", "Each multiset is mapped to the digit multiset of (descending - ascending), computed digit by digit with borrows."),
      note("kaprekar.cycles", "Find every cycle", `Following the map from every multiset finds ${r.attractors.length} nontrivial attractor(s) plus the trivial fixed point 0 of the repdigits.`),
      note("kaprekar.basins", "Count basins exactly", "Each multiset contributes its multinomial number of strings (and of strings with a nonzero leading digit) to its attractor."),
    ];
    const checks = [];
    // independent: re-iterate each cycle from its first member with the direct (string-sorting) step
    for (const a of r.attractors) {
      let x = a.members[0]; const seen = [x];
      for (let i = 0; i < a.length; i++) { x = kaprekarStep(x, d, b); seen.push(x); }
      const okc = seen[a.length] === a.members[0] && new Set(seen.slice(0, a.length).map(String)).size === a.length && seen.slice(0, a.length).every((v) => a.members.includes(v));
      checks.push(check("cycle re-iteration", okc, `${a.membersText[0]}: direct iteration returns after ${a.length} step(s)`));
    }
    // totals add up
    const B = BigInt(b), D = BigInt(d);
    let sumAll = r.repdigits.all + (r.zeroBasin ? r.zeroBasin.all : 0n), sumProper = r.repdigits.proper + (r.zeroBasin ? r.zeroBasin.proper : 0n);
    for (const a of r.attractors) { sumAll += a.basinAll; sumProper += a.basinProper; }
    checks.push(check("basin totals", sumAll === B ** D && sumProper === (B - 1n) * B ** (D - 1n), `basins + repdigits = ${b}^${d} strings (and ${b - 1} * ${b}^${d - 1} with nonzero leading digit)`, "exact count"));
    // random starting numbers iterated directly
    const cycleNums = new Set(r.attractors.flatMap((a) => a.members.map(String)));
    const rnd = prng(d * 131 + b);
    let sampleOk = true, sampled = 0;
    const maxN = B ** D;
    for (let i = 0; i < 150; i++) {
      let x = BigInt(Math.floor(rnd() * 2 ** 26)) * BigInt(Math.floor(rnd() * 2 ** 26)) % maxN;
      const ds = formatFixed(x, d, b); if (/^(.)\1*$/.test(ds)) continue;
      let k = 0; while (!cycleNums.has(String(x)) && k <= r.maxSteps + 1) { x = kaprekarStep(x, d, b); k++; }
      sampled++; if (k > r.maxSteps || !cycleNums.has(String(x))) sampleOk = false;
    }
    checks.push(check("random starts", sampleOk, `${sampled} random non-repdigit starts, iterated directly, all enter a listed attractor within ${r.maxSteps} steps`));
    if (r.maxStepsExample !== null) {
      let x = r.maxStepsExample, k = 0; while (!cycleNums.has(String(x)) && k <= r.maxSteps + 1) { x = kaprekarStep(x, d, b); k++; }
      checks.push(check("longest orbit", k === r.maxSteps, `${formatFixed(r.maxStepsExample, d, b)} needs exactly ${k} steps (reported maximum ${r.maxSteps})`));
    }
    return { family: "kaprekar", answers, solutionStatus: "exact", checks, steps,
      extra: { card: CARDS.kaprekar, table: { columns: ["type", "members", "basinProper", "basinAll", "maxSteps"], rows }, stepHistogram: r.stepHistogram.map((h) => ({ steps: h.steps, count: String(h.count) })), convention: r.convention, repdigits: { all: String(r.repdigits.all), proper: String(r.repdigits.proper) }, zeroBasin: r.zeroBasin && { all: String(r.zeroBasin.all), proper: String(r.zeroBasin.proper) }, multisets: r.multisets, ms: r.ms, raw: r } };
  },

  collatz(args, budget) {
    const r = collatz(args.n, { budget, pathCap: args.pathCap ?? 1000 });
    const answers = [
      { kind: "exact", label: "Steps to reach 1", text: String(r.steps), tree: intTree(r.steps) },
      { kind: "exact", label: "Highest value reached", text: String(r.peak), tree: intTree(r.peak) },
      { kind: "exact", label: "Stopping time (first value below the start)", text: String(r.stoppingTime) },
      { kind: "info", label: "Scope", text: `This computes the trajectory of ${r.n} only. The Collatz conjecture for all n remains open.` },
    ];
    // independent: shortcut map T(n) = (3n + 1)/2 for odd n counts 2 steps; plain Number arithmetic when safe
    let x = r.n, k = 0, peak = x;
    while (x !== 1n) { if (x & 1n) { x = (3n * x + 1n); if (x > peak) peak = x; x /= 2n; k += 2; } else { x /= 2n; k++; } budget.tick(1); }
    const checks = [check("recount with the shortcut map", k === r.steps && peak === r.peak, `(3n + 1)/2 shortcut gives ${k} steps and peak ${peak}`)];
    return { family: "collatz", answers, solutionStatus: "exact", checks,
      steps: [note("collatz.iterate", "Iterate the map", "Apply n -> n/2 (even) or n -> 3n + 1 (odd) with exact integers until 1 is reached.")],
      extra: { card: CARDS.collatz, path: r.path.map(String), pathTruncated: r.pathTruncated, oddSteps: r.oddSteps, evenSteps: r.evenSteps, peakAt: r.peakAt, table: { columns: ["step", "value"], rows: r.path.slice(0, 200).map((v, i) => ({ step: i, value: String(v) })) } } };
  },

  collatzVerify(args, budget) {
    const r = collatzVerify(args.N ?? DEFAULTS.collatzVerify, { budget });
    const answers = [
      { kind: "exact", label: "Bounded statement (exhaustive)", text: `Every n with 1 <= n <= ${fmtInt(r.N)} reaches 1.` },
      { kind: "exact", label: "Longest trajectory", text: `n = ${fmtInt(r.longest.n)} takes ${r.longest.steps} steps` },
      { kind: "exact", label: "Highest peak", text: `n = ${fmtInt(r.highest.n)} reaches ${fmtInt(r.highest.peak)}` },
      { kind: "evidence", label: "Collatz conjecture", text: `Verified for all n <= ${fmtInt(r.N)}; the conjecture remains open (verified by others far beyond this bound, up to 2^68). ${EVIDENCE}`, bound: String(r.N) },
    ];
    const checks = [];
    const recs = [...r.stepRecords.slice(-4), r.longest];
    for (const s of recs) { const c = collatz(s.n, { budget, pathCap: 0 }); checks.push(check("record recomputed", c.steps === s.steps, `n = ${s.n}: BigInt iteration gives ${c.steps} steps`)); }
    for (const p of r.peakRecords.slice(-3)) { const c = collatz(p.n, { budget, pathCap: 0 }); checks.push(check("peak recomputed", Number(c.peak) === p.peak, `n = ${p.n}: BigInt iteration peaks at ${c.peak}`)); }
    const rnd = prng(r.N % 100000 + 7);
    let allOk = true;
    for (let i = 0; i < 50; i++) { const n = 1 + Math.floor(rnd() * r.N); const c = collatz(n, { budget, pathCap: 0 }); if (!c.reachedOne) allOk = false; }
    checks.push(check("random spot checks", allOk, "50 random n <= N re-iterated from scratch in BigInt all reach 1"));
    return { family: "collatz", answers, solutionStatus: "evidence", checks,
      steps: [note("collatz.descent", "Descent method", "Each n is iterated only until it drops below n: every smaller value has already been verified, so reaching a smaller value implies that n reaches 1 as well."),
        note("collatz.records", "Records", "Total step counts are memoised; a peak record can only come from the part of the orbit before it drops below n.")],
      extra: { card: CARDS.collatz, table: { columns: ["n", "steps"], rows: r.stepRecords.map((s) => ({ n: s.n, steps: s.steps })) }, peakRecords: r.peakRecords.map((p) => ({ n: p.n, peak: p.peak })), ms: r.ms, method: r.method } };
  },

  goldbach(args, budget) {
    const r = goldbach(args.n, { budget });
    if (!r.ok) return { family: "goldbach", answers: [{ kind: "none", label: r.reason }], solutionStatus: "unsupported", checks: [], extra: { card: CARDS.goldbach } };
    const proven = r.deterministic;
    const answers = [
      { kind: "exact", label: "Decomposition", text: `${r.n} = ${r.p} + ${r.q}`, tree: X.add(X.num(r.p), X.num(r.q)) },
      { kind: "info", label: "Primality of the larger part", text: proven ? `${r.q} is prime (${r.method}).` : `${r.q} is a probable prime (${r.method}); this decomposition is not certified.` },
      { kind: "info", label: "Scope", text: "One decomposition of one number. The Goldbach conjecture for all even numbers remains open." },
    ];
    const qn = BigInt(r.q);
    const second = qn < 10n ** 12n ? { prime: isPrimeTrial(qn), proven: true } : isPrimeMR2(qn);
    const checks = [
      check("sum", r.p + r.q === r.n, `${r.p} + ${r.q} = ${r.n}`, "exact"),
      check("p prime (trial division)", isPrimeTrial(r.p), `${r.p} has no divisor up to its square root`),
      check(qn < 10n ** 12n ? "q prime (trial division)" : "q prime (second Miller-Rabin implementation)", second.prime, second.proven ? "independent primality routine agrees" : "independent strong probable-prime test agrees (not a certificate)"),
    ];
    return { family: "goldbach", answers, solutionStatus: proven ? "exact" : "partial", checks,
      steps: [note("goldbach.search", "Search small primes p", `Try p = 3, 5, 7, ... and test n - p for primality; found after ${r.tries} tries.`)],
      extra: { card: CARDS.goldbach, p: String(r.p), q: String(r.q), tries: r.tries } };
  },

  goldbachVerify(args, budget) {
    const r = goldbachVerify(args.N ?? DEFAULTS.goldbachVerify, { budget });
    if (!r.allHold) return { family: "goldbach", answers: [{ kind: "none", label: `Unverified cases were found (${r.failures.slice(0, 5).join(", ")}); they must be re-checked independently before any conclusion.` }], solutionStatus: "partial", checks: [check("all even n decomposed", false, "some cases failed")], extra: { raw: r } };
    const answers = [
      { kind: "exact", label: "Bounded statement (exhaustive)", text: `Every even n with 4 <= n <= ${fmtInt(r.N)} is a sum of two primes.` },
      { kind: "exact", label: "Hardest case (largest least prime)", text: `${fmtInt(r.hardest.n)} = ${r.hardest.p} + ${fmtInt(r.hardest.q)}; no smaller prime p works` },
      { kind: "exact", label: "Average least prime", text: r.meanMinP.toFixed(3) },
      { kind: "evidence", label: "Goldbach conjecture", text: `Verified for every even n <= ${fmtInt(r.N)}; the conjecture remains open (verified by others up to 4 * 10^18). ${EVIDENCE}`, bound: String(r.N) },
    ];
    const checks = [];
    let sampleOk = true;
    for (const s of r.sample) if (!(isPrimeTrial(s.p) && isPrimeTrial(s.q) && s.p + s.q === s.n)) sampleOk = false;
    checks.push(check("sample re-verified", sampleOk, `${r.sample.length} decompositions (spread over the range) re-checked by trial division, a different primality routine`));
    // minimality of the hardest case
    let minimal = true;
    for (let p = 2; p < r.hardest.p; p++) if (isPrimeTrial(p) && isPrimeTrial(r.hardest.n - p)) { minimal = false; break; }
    checks.push(check("hardest case is minimal", minimal, `for every prime p < ${r.hardest.p}, ${r.hardest.n} - p is composite (trial division)`));
    let recOk = true;
    for (const rec of r.records.slice(-5)) if (!(isPrimeTrial(rec.p) && isPrimeTrial(rec.q))) recOk = false;
    checks.push(check("records re-verified", recOk, "the last record decompositions are prime pairs by trial division"));
    return { family: "goldbach", answers, solutionStatus: "evidence", checks,
      steps: [note("goldbach.sieve", "Segmented sieve", "Sieve primes in windows that cover n - p for the small primes p."),
        note("goldbach.least", "Least prime", "For each even n try p = 3, 5, 7, ... until n - p is prime; record the least such p.")],
      extra: { card: CARDS.goldbach, table: { columns: ["n", "p", "q"], rows: r.records.map((x) => ({ n: x.n, p: x.p, q: x.q })) }, minPHistogram: r.minPHistogram, ms: r.ms, method: r.method } };
  },

  twinPrimes(args, budget) { return primesResult(args, budget, "twin"); },
  primeGaps(args, budget) { return primesResult(args, budget, "gaps"); },

  zetaZeros(args, budget) {
    let Tq = args.T !== undefined ? Number(args.T) : null;
    if (args.count !== undefined) {
      const c = Math.max(1, Math.floor(Number(args.count)));
      // Riemann-von Mangoldt: choose a height that contains at least c zeros, then trim
      let lo = 14, hi = 20;
      const Napprox = (t) => (t / (2 * Math.PI)) * Math.log(t / (2 * Math.PI * Math.E)) + 7 / 8;
      while (Napprox(hi) < c + 3) hi *= 1.5;
      for (let i = 0; i < 60; i++) { const m = (lo + hi) / 2; if (Napprox(m) < c + 3) lo = m; else hi = m; }
      Tq = hi + 2;
    }
    if (Tq === null) Tq = DEFAULTS.zetaZeros;
    const r = zetaZeros(Tq, { budget });
    let zeros = r.zeros, Tshow = r.T;
    const all = r.allOnCriticalLine;
    const answers = [];
    const shown = args.count !== undefined ? zeros.slice(0, Number(args.count)) : zeros;
    for (const z of shown.slice(0, 10)) answers.push({ kind: "approx", label: "zero: 1/2 + i t, t =", approx: { value: z.toFixed(12), digits: 12, requested: 12, errorBound: "1e-10", method: z < RS_THRESHOLD ? "Euler-Maclaurin + Brent" : "Riemann-Siegel + Brent", converged: true } });
    answers.push({ kind: "exact", label: "Zeros found on the critical line", text: `${r.count} sign changes of Z(t) for 0 < t < ${Tshow}` });
    answers.push({ kind: "exact", label: "Riemann-von Mangoldt count N(T)", text: `N(${Tshow}) = ${r.rvm.count} (theta(T)/pi + 1 + S(T) = ${r.rvm.estimate.toFixed(6)})` });
    answers.push({ kind: "evidence", label: "Riemann hypothesis",
      text: all ? `All ${r.count} nontrivial zeros with 0 < Im s < ${Tshow} lie on the critical line Re s = 1/2 and are simple (numerical, double precision). The hypothesis remains open; it has been checked by others to far greater heights. ${EVIDENCE}`
        : `The counts did not match (${r.count} sign changes vs N(T) = ${r.rvm.count}); the check is inconclusive at this height and nothing is concluded.`, bound: String(Tshow) });
    const checks = [];
    // each zero: Z changes sign across it
    const idx = zeros.length <= 400 ? zeros.map((_, i) => i) : Array.from({ length: 400 }, (_, i) => Math.floor((i * zeros.length) / 400));
    let signOk = true;
    for (const i of idx) { const z = zeros[i], d = Math.max(1e-7, 1e-9 * z); if (Math.sign(Z(z - d)) === Math.sign(Z(z + d))) signOk = false; budget.tick(20); }
    checks.push(check("sign change at each zero", signOk, `Z(t - delta) and Z(t + delta) have opposite signs for ${idx.length} zeros`));
    // alternative formula: Riemann-Siegel vs Euler-Maclaurin at sample zeros where both are accurate
    const alt = zeros.filter((z) => z > 60 && z < 3000);
    if (alt.length) {
      let mx = 0; const pick = alt.filter((_, i) => i % Math.max(1, Math.floor(alt.length / 20)) === 0);
      for (const z of pick) { mx = Math.max(mx, Math.abs(ZEM(z)), Math.abs(ZRS(z))); budget.tick(3000); }
      checks.push(check("second formula", mx < 1e-5, `Euler-Maclaurin and Riemann-Siegel both give |Z| < ${mx.toExponential(1)} at ${pick.length} of the zeros`));
    }
    if (zeros.length >= 3) {
      const k = Math.min(zeros.length, KNOWN_ZEROS.length);
      let mx = 0; for (let i = 0; i < k; i++) mx = Math.max(mx, Math.abs(zeros[i] - KNOWN_ZEROS[i]));
      checks.push(check("published values", mx < 1e-9, `first ${k} zeros agree with Odlyzko's tables to ${mx.toExponential(1)}`, "reference"));
    }
    checks.push(check("count matches N(T)", r.rvm.count === r.zeros.filter((z) => z < r.rvm.T).length && r.rvm.residual < 0.25, `argument principle gives N(T) = ${r.rvm.count} (distance to nearest integer ${r.rvm.residual.toExponential(1)})`));
    if (r.turing.applied) checks.push(check("Turing's method", r.turing.agrees, `N(g_${r.turing.gramIndex}) = ${r.turing.expected} from ${r.turing.blocksUsed} Rosser block(s); ${r.turing.signChangesBelow} sign changes found below g_${r.turing.gramIndex} = ${r.turing.g.toFixed(4)}`));
    checks.push(check("Rosser's rule", r.rosserFailures.length === 0, r.rosserFailures.length ? `${r.rosserFailures.length} Gram block(s) with missing sign changes after refinement` : `all ${r.gramBlocks} Gram blocks contain the expected number of sign changes`));
    const res = { family: "riemann", answers, solutionStatus: all ? "evidence" : "partial", checks,
      steps: [note("zeta.Z", "Hardy's Z function", "Z(t) = exp(i theta(t)) zeta(1/2 + i t) is real, and |Z(t)| = |zeta(1/2 + i t)|; every sign change of Z is a zero on the critical line."),
        note("zeta.gram", "Gram points", `Evaluate Z at the ${r.gramPoints} Gram points g_n (theta(g_n) = n pi); where Gram's law fails (${r.gramLawViolations} blocks), subdivide the Gram block until it shows the expected sign changes.`),
        note("zeta.brent", "Refine", "Each sign change is refined with Brent's method."),
        note("zeta.count", "Count all zeros", "N(T) = theta(T)/pi + 1 + S(T), with S(T) from the continuous change of arg zeta along 2 -> 2 + iT -> 1/2 + iT. If the number of sign changes equals N(T), no zero can lie off the line (off-line zeros come in pairs and would be extra).")],
      extra: { card: CARDS.riemann, table: { columns: ["n", "t"], rows: zeros.slice(0, 2000).map((z, i) => ({ n: i + 1, t: z.toFixed(12) })) }, count: r.count, rvm: r.rvm, turing: r.turing, gramLawViolations: r.gramLawViolations, method: r.method, precision: r.precision, ms: r.ms } };
    return res;
  },

  zeta(args, budget) {
    const s = [Number(args.re ?? 0), Number(args.im ?? 0)];
    if (s[0] === 1 && s[1] === 0) return { family: "zeta", answers: [{ kind: "none", label: "zeta has a simple pole at s = 1 (the harmonic series diverges)." }], solutionStatus: "exact", checks: [] };
    const v = zeta(s);
    budget.tick(Math.abs(s[1]) + 50);
    const txt = fmtComplex([+v[0].toPrecision(15), +v[1].toPrecision(15)]);
    const checks = [];
    if (s[0] >= 0) {
      // same summation with a different cut-off N must agree (convergence check)
      const w = zetaEM(s); const shifted = zetaShifted(s);
      checks.push(check("different summation cut-off", Math.hypot(w[0] - shifted[0], w[1] - shifted[1]) < 1e-10 * Math.max(1, Math.hypot(w[0], w[1])), "Euler-Maclaurin with another cut-off agrees to 1e-10"));
    }
    if (s[1] === 0 && Number.isInteger(s[0]) && s[0] >= 2 && s[0] % 2 === 0 && s[0] <= 12) {
      const exact = { 2: Math.PI ** 2 / 6, 4: Math.PI ** 4 / 90, 6: Math.PI ** 6 / 945, 8: Math.PI ** 8 / 9450, 10: Math.PI ** 10 / 93555, 12: 691 * Math.PI ** 12 / 638512875 }[s[0]];
      checks.push(check("closed form", Math.abs(v[0] - exact) < 1e-13, `agrees with the Euler closed form (${exact})`, "reference"));
    }
    return { family: "zeta", answers: [{ kind: "approx", label: `zeta(${fmtComplex(s)})`, approx: { value: txt, digits: 14, requested: 14, errorBound: "1e-12 (relative, typical)", method: s[0] < 0 ? "functional equation + Euler-Maclaurin" : "Euler-Maclaurin", converged: true } }],
      solutionStatus: "approximate", checks, extra: { value: v } };
  },

  eulerBricks(args, budget) {
    const r = eulerBricks(args.maxEdge ?? DEFAULTS.eulerBricks, { budget });
    const first = r.bricks.slice(0, 8).map((b) => `(${b.a}, ${b.b}, ${b.c})`).join(", ");
    const answers = [
      { kind: "exact", label: "Euler bricks found (exhaustive)", text: `${r.count} Euler bricks with largest edge <= ${fmtInt(r.maxEdge)} (${r.primitiveCount} primitive)${r.count ? `; smallest: ${first}` : ""}` },
      { kind: "exact", label: "Perfect cuboids", text: r.perfectCuboids.length ? `CANDIDATE: ${r.perfectCuboids.map((b) => `(${b.a}, ${b.b}, ${b.c})`).join(", ")} - requires independent confirmation` : `None: no perfect cuboid has largest edge <= ${fmtInt(r.maxEdge)}.` },
      { kind: "evidence", label: "Perfect cuboid problem", text: `No perfect cuboid with largest edge <= ${fmtInt(r.maxEdge)}. The problem remains open; searches by others go far beyond this bound. ${EVIDENCE}`, bound: String(r.maxEdge) },
    ];
    const checks = [];
    let allOk = true;
    for (const b of r.bricks) {
      const [A, Bv, C] = [BigInt(b.a), BigInt(b.b), BigInt(b.c)];
      const sq = (v) => { const q = isqrtBig(v); return q * q === v; };
      if (!(sq(A * A + Bv * Bv) && sq(A * A + C * C) && sq(Bv * Bv + C * C))) allOk = false;
      if (sq(A * A + Bv * Bv + C * C) !== (b.space !== null)) allOk = false;
    }
    checks.push(check("each brick re-checked", allOk, `${r.bricks.length} bricks: all three face diagonals verified with exact BigInt square roots; space diagonals re-tested`));
    const L0 = Math.min(r.maxEdge, 400);
    const bf = eulerBricksBrute(L0);
    const mine = r.bricks.filter((b) => b.c <= L0).map((b) => `${b.a},${b.b},${b.c}`).sort().join(";");
    checks.push(check("brute force below 400", bf.map((x) => x.join(",")).sort().join(";") === mine, `a triple loop over all edges <= ${L0} finds the same ${bf.length} brick(s)`));
    return { family: "eulerbrick", answers, solutionStatus: "evidence", checks,
      steps: [note("brick.pairs", "Pythagorean pairs", `Generate all ${fmtInt(r.pythagoreanPairs)} leg pairs (x, y) <= L with x^2 + y^2 a square (Euclid's formula and multiples).`),
        note("brick.triangles", "Triangles in the pair graph", "An Euler brick is a triangle a-b-c in which every pair is Pythagorean."),
        note("brick.space", "Space diagonal", "Each brick is tested for an integer space diagonal sqrt(a^2 + b^2 + c^2).")],
      extra: { card: CARDS.eulerbrick, table: { columns: ["a", "b", "c", "dab", "dac", "dbc", "primitive"], rows: r.bricks.slice(0, 500).map((b) => ({ a: b.a, b: b.b, c: b.c, dab: b.dab, dac: b.dac, dbc: b.dbc, primitive: b.primitive })) }, nearMisses: r.nearMisses.map((b) => ({ a: b.a, b: b.b, c: b.c, spaceDiagonal: b.spaceDiagonal })), ms: r.ms } };
  },

  sofa(args, budget) {
    const r = movingSofa({ budget });
    const answers = [
      { kind: "exact", label: "Semicircle (area)", text: "pi/2 = 1.5707963267948966", tree: X.mul(X.HALF, X.PI) },
      { kind: "exact", label: "Hammersley's sofa (area)", text: `pi/2 + 2/pi = ${r.hammersley.value}`, tree: X.add(X.mul(X.HALF, X.PI), X.mul(X.TWO, X.pow(X.PI, X.NEG_ONE))) },
      { kind: "info", label: "Gerver's sofa (area, from the literature)", text: `about ${r.gerver.value} (Gerver 1992; value as reported by Romik 2018). Quelvra recomputes Gerver's defining parameters A = ${r.gerver.parameters.A.toFixed(12)}, B = ${r.gerver.parameters.B.toFixed(12)}, phi = ${r.gerver.parameters.phi.toFixed(12)}, theta = ${r.gerver.parameters.theta.toFixed(12)} but does not recompute the area itself.` },
      { kind: "info", label: "Best known upper bound", text: `${r.upperBound.value} (${r.upperBound.source})` },
      { kind: "info", label: "Status", text: r.status },
    ];
    const g = r.gerver.parameters;
    const checks = [
      check("Hammersley by quadrature", Math.abs(hammersleyAreaNumeric() - (Math.PI / 2 + 2 / Math.PI)) < 1e-12, "numerical integration of the shape's height profile matches pi/2 + 2/pi"),
      check("Gerver parameters", g.residual < 1e-12 && Math.abs(g.A - 0.094426560843653) < 1e-10 && Math.abs(g.B - 1.399203727333547) < 1e-10 && Math.abs(g.phi - 0.039177364790084) < 1e-10 && Math.abs(g.theta - 0.681301509382725) < 1e-10, `Newton solution (residual ${g.residual.toExponential(1)}) matches the published values`, "reference"),
      check("ordering", Math.PI / 2 < r.hammersley.value && r.hammersley.value < Number(r.gerver.value) && Number(r.gerver.value) < 2.37, "semicircle < Hammersley < Gerver < 2.37"),
    ];
    return { family: "sofa", answers, solutionStatus: "open-problem", checks, extra: { card: CARDS.sofa, raw: r } };
  },

  card(args) {
    const card = CARDS[args.id];
    if (!card) throw Object.assign(new Error(`no card named ${args.id}`), { code: "UNSUPPORTED" });
    const answers = [];
    if (args.askedForProof) answers.push({ kind: "info", label: "About proving it", text: honestNote(card) });
    answers.push({ kind: "info", label: card.title, text: card.statement });
    answers.push({ kind: "info", label: "Status", text: card.status });
    return { family: card.id, answers, solutionStatus: card.open ? "open-problem" : "info", checks: [], extra: { card, honest: args.askedForProof ? honestNote(card) : null } };
  },
};

function zetaShifted(s) {
  // Euler-Maclaurin with the cut-off moved by 37 terms (independent truncation), 12 correction terms
  const B2K = [1 / 6, -1 / 30, 1 / 42, -1 / 30, 5 / 66, -691 / 2730, 7 / 6, -3617 / 510, 43867 / 798, -174611 / 330, 854513 / 138, -236364091 / 2730];
  let f = 1; const F = [1]; for (let i = 1; i <= 26; i++) F.push((f *= i));
  const N = Math.max(12, Math.ceil(Math.hypot(s[0], s[1]) + 10)) + 37;
  let re = 0, im = 0;
  const np = (n) => { const l = Math.log(n), m = Math.exp(-s[0] * l), ph = -s[1] * l; return [m * Math.cos(ph), m * Math.sin(ph)]; };
  for (let n = 1; n < N; n++) { const v = np(n); re += v[0]; im += v[1]; }
  const Ns = np(N);
  const a = [Ns[0] * N, Ns[1] * N], d = [s[0] - 1, s[1]], dd = d[0] * d[0] + d[1] * d[1];
  re += (a[0] * d[0] + a[1] * d[1]) / dd; im += (a[1] * d[0] - a[0] * d[1]) / dd;
  re += Ns[0] / 2; im += Ns[1] / 2;
  let poch = [s[0], s[1]], pw = [Ns[0] / N, Ns[1] / N];
  const mul = (x, y) => [x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0]];
  for (let k = 1; k <= 12; k++) {
    const c = B2K[k - 1] / F[2 * k], tm = mul(poch, pw);
    re += c * tm[0]; im += c * tm[1];
    poch = mul(poch, mul([s[0] + 2 * k - 1, s[1]], [s[0] + 2 * k, s[1]]));
    pw = [pw[0] / (N * N), pw[1] / (N * N)];
  }
  return [re, im];
}

function primesResult(args, budget, which) {
  const r = primeStats(args.N ?? DEFAULTS.twinPrimes, { budget });
  const N = r.N;
  const answers = which === "twin" ? [
    { kind: "exact", label: "Twin prime pairs (p, p + 2) with p + 2 <= N", text: `pi_2(${fmtInt(N)}) = ${fmtInt(r.twinCount)}`, tree: intTree(r.twinCount) },
    { kind: "exact", label: "Primes up to N", text: `pi(${fmtInt(N)}) = ${fmtInt(r.pi)}` },
    { kind: "exact", label: "First and last pairs", text: `${r.firstPairs.slice(0, 5).map((p) => `(${p[0]}, ${p[1]})`).join(", ")} ... ${r.lastPairs.slice(-3).map((p) => `(${p[0]}, ${p[1]})`).join(", ")}` },
    { kind: "approx", label: "Partial Brun sum (sum of 1/p + 1/(p+2) over these pairs)", approx: { value: r.brunPartial.toFixed(12), digits: 12, requested: 12, errorBound: "1e-12", method: "compensated summation", converged: true } },
    { kind: "evidence", label: "Twin prime conjecture", text: `Twin primes keep appearing up to ${fmtInt(N)}, but no finite count can show there are infinitely many. The conjecture remains open (bounded gaps: at most 246 infinitely often, Polymath 2014). ${EVIDENCE}`, bound: String(N) },
  ] : [
    { kind: "exact", label: "Largest gap between consecutive primes up to N", text: r.maxGap ? `${r.maxGap.gap} (between ${fmtInt(r.maxGap.after)} and ${fmtInt(r.maxGap.before)})` : "none" },
    { kind: "exact", label: "Maximal gap records", text: r.gapRecords.map((g) => `${g.gap} after ${g.after}`).join(", ") },
    { kind: "info", label: "Context", text: "Maximal prime gaps grow roughly like (ln p)^2 (Cramer's conjecture, open). Infinitely many gaps are at most 246 (Polymath 2014)." },
  ];
  const checks = [];
  if (KNOWN_PI[N] !== undefined) checks.push(check("pi(N) reference value", r.pi === KNOWN_PI[N], `pi(${N}) = ${KNOWN_PI[N]} (published)`, "reference"));
  if (KNOWN_PI2[N] !== undefined) checks.push(check("pi_2(N) reference value", r.twinCount === KNOWN_PI2[N], `pi_2(${N}) = ${KNOWN_PI2[N]} (published)`, "reference"));
  // independent recount of the tail with Miller-Rabin
  const lo = Math.max(2, N - 3000);
  const tail = [];
  for (let p = lo; p + 2 <= N; p++) if (T.isPrime(p) && T.isPrime(p + 2)) tail.push([p, p + 2]);
  const lastMine = r.lastPairs.filter((p) => p[0] >= lo).map(String).join(";");
  checks.push(check("last pairs recomputed", tail.slice(-10).map(String).join(";") === lastMine, `twin pairs in [${lo}, ${N}] recomputed with Miller-Rabin agree`));
  let gapOk = true;
  for (const g of r.gapRecords.slice(-6)) {
    if (!(T.isPrime(g.after) && T.isPrime(g.before))) gapOk = false;
    for (let x = g.after + 1; x < g.before && gapOk; x++) if (T.isPrime(x)) gapOk = false;
  }
  checks.push(check("gap records re-checked", gapOk, "endpoints prime and no prime strictly inside, by Miller-Rabin"));
  return { family: which === "twin" ? "twinprimes" : "primegaps", answers, solutionStatus: which === "twin" ? "evidence" : "exact", checks,
    steps: [note("primes.sieve", "Segmented sieve of Eratosthenes", `Sieve [0, ${fmtInt(N)}] in windows of 2^18 using primes up to sqrt(N).`)],
    extra: { card: CARDS.twinprimes, table: which === "twin" ? { columns: ["p", "p + 2"], rows: [...r.firstPairs, ...r.lastPairs].map((p) => ({ p: p[0], "p + 2": p[1] })) } : { columns: ["gap", "after", "before"], rows: r.gapRecords }, pi: r.pi, twinCount: r.twinCount, brunPartial: r.brunPartial, gapRecords: r.gapRecords, ms: r.ms } };
}

export const RESEARCH_COMMANDS = Object.keys(RUN);

// runResearch(command, args, opts): opts = { timeMs, deadline, ops, onProgress }
export function runResearch(command, args = {}, opts = {}) {
  const t0 = now();
  const label = opts.label || `${command}(${Object.values(args).map(String).join(", ")})`;
  const fn = RUN[command];
  if (!fn) return failResult(command, label, Object.assign(new Error(`unknown research command "${command}"`), { code: "UNSUPPORTED" }), t0);
  const budget = new Budget({ timeMs: opts.timeMs ?? 20000, deadline: opts.deadline, ops: opts.ops, onProgress: opts.onProgress, what: command });
  try {
    const c = fn(args, budget);
    const res = mkResult({ command, label, t0, ...c });
    if (res.verification.status === "failed") {
      // never report an answer whose independent re-check failed
      res.ok = false;
      res.answers = [{ kind: "none", label: "An independent re-check failed, so no result is reported. Quelvra does not guess." }];
      res.solutionStatus = "unsolved";
    }
    return res;
  } catch (e) {
    if (opts.debug && !(e && e.code)) throw e;
    return failResult(command, label, e, t0);
  }
}

// Convenience: English/command text straight to a result (null when not recognised).
export function solveResearch(text, opts = {}) {
  const r = recogniseResearch(text);
  if (!r) return null;
  const out = runResearch(r.command, r.args, { ...opts, label: r.label });
  out.input.original = text;
  out.input.interpretation = r.label;
  return out;
}

// ------------------------------------------------------------------ orchestrator strategy
// Parsed calls such as collatz(27), kaprekar(5), goldbachverify(10^6), zetazeros(100), eulerbricks(1000).
export const RESEARCH_FUNCTIONS = {
  kaprekar: (a) => ({ command: "kaprekar", args: { digits: a[0] ?? 4, base: a[1] ?? 10 } }),
  collatz: (a) => ({ command: "collatz", args: { n: a[0] } }),
  collatzverify: (a) => ({ command: "collatzVerify", args: { N: a[0] } }),
  goldbach: (a) => ({ command: "goldbach", args: { n: a[0] } }),
  goldbachverify: (a) => ({ command: "goldbachVerify", args: { N: a[0] } }),
  twinprimes: (a) => ({ command: "twinPrimes", args: { N: a[0] } }),
  primegaps: (a) => ({ command: "primeGaps", args: { N: a[0] } }),
  zetazeros: (a) => ({ command: "zetaZeros", args: { T: a[0] !== undefined ? Number(a[0]) : undefined } }),
  eulerbricks: (a) => ({ command: "eulerBricks", args: { maxEdge: a[0] } }),
  movingsofa: () => ({ command: "sofa", args: {} }),
};
register({
  id: "research", kinds: ["command"], priority: 25,
  applies: (card) => card.command in RESEARCH_FUNCTIONS,
  run(node, card, env) {
    const vals = (node.args || []).map((a) => { const s = simplify(a); return X.isInt(s) ? s.v.n : X.isNum(s) ? Number(s.v.n) / Number(s.v.d) : null; });
    if (vals.some((v) => v === null)) return null;
    const { command, args } = RESEARCH_FUNCTIONS[card.command](vals);
    for (const k of Object.keys(args)) if (args[k] === undefined) delete args[k];
    const r = runResearch(command, args, { deadline: env.deadline });
    if (!r.ok) { const e = new Error(r.answers[0] && r.answers[0].label); e.code = r.error && r.error.code === "UNSUPPORTED" ? "UNSUPPORTED" : r.error && r.error.code || "UNSUPPORTED"; throw e; }
    return { answers: r.answers, steps: r.steps, solutionStatus: r.solutionStatus, extra: { ...r.extra, classification: r.classification }, note: r.classification.label, verify: () => r.verification };
  },
});
