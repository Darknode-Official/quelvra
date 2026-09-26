import { test, eq, ok, close, throws } from "./harness.js";
import * as X from "../public/engine/expr.js";
import { strategies } from "../public/engine/orchestrate.js";
import { kaprekar, kaprekarBrute, kaprekarStep, formatFixed } from "../public/engine/research/kaprekar.js";
import { collatz, collatzVerify } from "../public/engine/research/collatz.js";
import { goldbach, goldbachVerify, primeStats, isPrimeTrial, isPrimeMR2 } from "../public/engine/research/primes.js";
import { zetaZeros, zeta, Z, ZEM, ZRS, theta, gramPoint, KNOWN_ZEROS } from "../public/engine/research/zeta.js";
import { eulerBricks, eulerBricksBrute } from "../public/engine/research/bricks.js";
import { movingSofa, gerverParameters } from "../public/engine/research/sofa.js";
import { CARDS, honestyViolations, cardText } from "../public/engine/research/cards.js";
import { parseIntText } from "../public/engine/research/budget.js";
import { recogniseResearch, runResearch, solveResearch, DEFAULTS } from "../public/engine/strategies/research.js";

const S = (xs) => xs.map(String);
const text = (r) => JSON.stringify(r, (k, v) => (typeof v === "bigint" ? String(v) : k === "raw" ? undefined : v));

// ------------------------------------------------------------------ Kaprekar
// Independent brute force with plain Numbers (different code from the engine): cycles and basins by iteration.
function bruteKaprekar(d, b = 10) {
  const total = b ** d;
  const step = (x) => { const ds = []; for (let i = 0; i < d; i++) { ds.push(x % b); x = Math.floor(x / b); } ds.sort((p, q) => p - q); let lo = 0, hi = 0; for (let i = 0; i < d; i++) { lo = lo * b + ds[i]; hi = hi * b + ds[d - 1 - i]; } return hi - lo; };
  const isRep = (x) => { const r = x % b; for (let i = 0; i < d; i++) { if (x % b !== r) return false; x = Math.floor(x / b); } return true; };
  const cycOf = new Map(); // number -> cycle key
  const cycles = new Map();
  let maxSteps = 0;
  for (let x = 0; x < total; x++) {
    if (isRep(x)) continue;
    const seen = new Map(); let v = x, k = 0;
    while (!seen.has(v) && !cycOf.has(v)) { seen.set(v, k++); v = step(v); }
    if (!cycOf.has(v)) { const mem = []; let u = v; do { mem.push(u); u = step(u); } while (u !== v); const key = mem.slice().sort((p, q) => p - q).join(","); for (const m of mem) cycOf.set(m, key); cycles.set(key, { members: mem, basin: 0 }); }
    // steps to enter the cycle
    let s = 0, w = x; while (!cycOf.has(w)) { w = step(w); s++; }
    if (s > maxSteps) maxSteps = s;
    cycles.get(cycOf.get(w)).basin++;
  }
  return { cycles: [...cycles.entries()].map(([key, c]) => ({ key, basin: c.basin, length: c.members.length })), maxSteps };
}
const keyOf = (a) => a.members.map(Number).sort((p, q) => p - q).join(",");

test("research: Kaprekar 3 digits -> 495", () => {
  const r = kaprekar(3);
  eq(S(r.fixedPoints).join(), "495"); eq(r.cycles.length, 0); eq(r.maxSteps, 6);
  eq(r.status, "proved by exhaustive computation");
});
test("research: Kaprekar 4 digits -> 6174 within 7 steps, published step histogram", () => {
  const r = kaprekar(4);
  eq(S(r.fixedPoints).join(), "6174"); eq(r.cycles.length, 0); eq(r.maxSteps, 7);
  eq(String(r.attractors[0].basinProper), "8991"); eq(String(r.attractors[0].basinAll), "9990");
  eq(r.stepHistogram.map((h) => String(h.count)).join(), "1,383,576,2400,1272,1518,1656,2184");
  eq(String(r.repdigits.all), "10"); eq(String(r.repdigits.proper), "9");
});
test("research: Kaprekar 5 digits: no fixed point, three cycles, matches brute force over all 10^5 strings", () => {
  const r = kaprekar(5);
  eq(r.fixedPoints.length, 0); eq(r.cycles.length, 3);
  const want = new Set(["62964,71973,74943,83952", "61974,63954,75933,82962", "53955,59994"]);
  for (const c of r.cycles) ok(want.has(keyOf(c)), keyOf(c));
  const bf = bruteKaprekar(5);
  eq(bf.cycles.length, 3);
  for (const c of bf.cycles) { const mine = r.attractors.find((a) => keyOf(a) === c.key); ok(mine, c.key); eq(String(mine.basinAll), String(c.basin), `basin of ${c.key}`); }
  eq(r.maxSteps, bf.maxSteps);
  // the engine's own brute force (BigInt code path) agrees too
  const eb = kaprekarBrute(5).filter((c) => !(c.length === 1 && c[0] === 0)).map((c) => c.join(",")).sort();
  eq(eb.join(";"), r.attractors.map(keyOf).sort().join(";"));
});
test("research: Kaprekar 6 digits: 549945, 631764 and a 7-cycle (brute force over 10^6 strings)", () => {
  const r = kaprekar(6);
  eq(S(r.fixedPoints).sort().join(), "549945,631764");
  eq(r.cycles.length, 1); eq(r.cycles[0].length, 7);
  ok(S(r.cycles[0].members).includes("840852"));
  const bf = bruteKaprekar(6);
  eq(bf.cycles.length, 3); eq(r.maxSteps, bf.maxSteps);
  for (const c of bf.cycles) eq(String(r.attractors.find((a) => keyOf(a) === c.key).basinAll), String(c.basin));
});
test("research: Kaprekar other bases and digit counts match brute force", () => {
  for (const [d, b] of [[2, 10], [3, 5], [4, 6], [5, 7], [4, 16], [7, 3], [3, 10], [6, 4], [8, 3]]) {
    const r = kaprekar(d, b);
    const bf = bruteKaprekar(d, b);
    eq(r.attractors.map(keyOf).sort().join(";"), bf.cycles.map((c) => c.key).sort().join(";"), `cycles d=${d} b=${b}`);
    eq(r.maxSteps, bf.maxSteps, `max steps d=${d} b=${b}`);
    for (const c of bf.cycles) eq(String(r.attractors.find((a) => keyOf(a) === c.key).basinAll), String(c.basin), `basin d=${d} b=${b}`);
  }
});
test("research: Kaprekar fixed width keeps leading zeros (2 digits: 09 is in the cycle)", () => {
  const r = kaprekar(2);
  ok(r.cycles[0].membersText.includes("09"));
  eq(formatFixed(9n, 2), "09"); eq(kaprekarStep(1000n, 4), 999n);
});
test("research: Kaprekar scales via multisets (12 digits exact totals, 15 digits)", () => {
  const r = kaprekar(12);
  eq(String(r.totalAll), String(10n ** 12n)); eq(r.multisets, 293930);
  let sum = r.repdigits.all + (r.zeroBasin ? r.zeroBasin.all : 0n);
  for (const a of r.attractors) sum += a.basinAll;
  eq(String(sum), String(10n ** 12n));
  const r15 = kaprekar(15);
  eq(S(r15.fixedPoints).sort().join(), "555549999944445,864333197666532");
});
test("research: Kaprekar respects the time budget", () => {
  const r = runResearch("kaprekar", { digits: 18 }, { timeMs: 1 });
  eq(r.ok, false); ok(/Time limit|budget/i.test(r.answers[0].label));
});

// ------------------------------------------------------------------ Collatz
test("research: Collatz trajectories", () => {
  const r = collatz(27);
  eq(r.steps, 111); eq(r.peak, 9232n); eq(r.stoppingTime, 96); eq(r.path.length, 112); eq(r.path[1], 82n);
  eq(collatz(1).steps, 0); eq(collatz(97).steps, 118);
  const big = collatz(2n ** 100n + 1n);
  let x = 2n ** 100n + 1n, k = 0; while (x !== 1n) { x = x % 2n ? 3n * x + 1n : x / 2n; k++; }
  eq(big.steps, k);
  throws(() => collatz(0));
});
test("research: Collatz verification to 10^6 with records", () => {
  const r = collatzVerify(1000000);
  ok(r.allReachOne); eq(r.longest.n, 837799); eq(r.longest.steps, 524);
  eq(r.highest.n, 704511); eq(r.highest.peak, 56991483520);
  eq(r.stepRecords.slice(0, 8).map((s) => s.n).join(), "1,2,3,6,7,9,18,25");
});
test("research: Collatz verification agrees with direct iteration for n <= 20000", () => {
  const r = collatzVerify(20000);
  let best = 0, bestN = 1, peakBest = 1, peakN = 1;
  for (let n = 1; n <= 20000; n++) { let x = n, k = 0, pk = n; while (x !== 1) { x = x % 2 ? 3 * x + 1 : x / 2; k++; if (x > pk) pk = x; } if (k > best) { best = k; bestN = n; } if (pk > peakBest) { peakBest = pk; peakN = n; } }
  eq(r.longest.n, bestN); eq(r.longest.steps, best); eq(r.highest.n, peakN); eq(r.highest.peak, peakBest);
});

// ------------------------------------------------------------------ Goldbach
test("research: Goldbach verification to 10^6: hardest case 503222 = 523 + 502699", () => {
  const r = goldbachVerify(1000000);
  ok(r.allHold); eq(r.evensChecked, 499999);
  eq(r.hardest.n, 503222); eq(r.hardest.p, 523); eq(r.hardest.q, 502699);
  eq(r.records.map((x) => x.p).join(), "2,3,5,7,19,23,31,47,73,103,139,173,211,233,293,313,331,359,383,389,523");
  eq(r.records.map((x) => x.n).slice(0, 10).join(), "4,6,12,30,98,220,308,556,992,2642");
});
test("research: Goldbach least primes agree with naive search below 3000", () => {
  const r = goldbachVerify(3000);
  let hard = { n: 4, p: 2 };
  for (let n = 4; n <= 3000; n += 2) { let p = 2; while (!(isPrimeTrial(p) && isPrimeTrial(n - p))) p++; if (p > hard.p) hard = { n, p }; }
  eq(r.hardest.n, hard.n); eq(r.hardest.p, hard.p);
});
test("research: Goldbach decomposition of single numbers", () => {
  const r = goldbach(1000000);
  ok(r.ok); eq(r.p + r.q, 1000000n); ok(isPrimeTrial(r.p) && isPrimeTrial(r.q));
  const b = goldbach(10n ** 20n);
  ok(b.ok && b.deterministic); eq(b.p + b.q, 10n ** 20n); ok(isPrimeMR2(b.q).prime);
  const huge = goldbach(10n ** 30n + 2n);
  ok(huge.ok); eq(huge.deterministic, false); ok(/probable/.test(huge.qStatus));
  eq(goldbach(7).ok, false); ok(/Helfgott/.test(goldbach(7).reason));
  eq(goldbach(4).p, 2n);
});

// ------------------------------------------------------------------ twin primes, gaps
test("research: twin prime counts and prime counts match published values", () => {
  const want = { 1000: [168, 35], 10000: [1229, 205], 100000: [9592, 1224], 1000000: [78498, 8169] };
  for (const [N, [pi, pi2]] of Object.entries(want)) { const r = primeStats(Number(N)); eq(r.pi, pi, `pi(${N})`); eq(r.twinCount, pi2, `pi_2(${N})`); }
  const r = primeStats(1000000);
  eq(String(r.firstPairs[0]), "3,5"); eq(String(r.lastPairs[r.lastPairs.length - 1]), "999959,999961");
  ok(r.brunPartial > 1.71 && r.brunPartial < 1.711);
});
test("research: twin primes agree with trial division below 20000", () => {
  let c = 0; for (let p = 2; p + 2 <= 20000; p++) if (isPrimeTrial(p) && isPrimeTrial(p + 2)) c++;
  eq(primeStats(20000).twinCount, c);
});
test("research: maximal prime gaps below 10^6", () => {
  const r = primeStats(1000000);
  eq(r.gapRecords.map((g) => g.after).join(), "2,3,7,23,89,113,523,887,1129,1327,9551,15683,19609,31397,155921,360653,370261,492113");
  eq(r.maxGap.gap, 114);
});

// ------------------------------------------------------------------ zeta
test("research: zeta values", () => {
  close(zeta(2)[0], Math.PI ** 2 / 6, 1e-14); close(zeta(4)[0], Math.PI ** 4 / 90, 1e-14);
  close(zeta(-1)[0], -1 / 12, 1e-13); close(zeta(0)[0], -0.5, 1e-13); eq(zeta(-2)[0], 0);
  close(zeta(0.5)[0], -1.4603545088095868, 1e-12);
  const z = zeta([0.5, KNOWN_ZEROS[0]]); ok(Math.hypot(z[0], z[1]) < 1e-12);
  const w = zeta([2, 3]); close(w[0], 0.7980219851462757, 1e-12); close(w[1], -0.1137443080529385, 1e-12);
  throws(() => zeta(1));
});
test("research: theta, Gram points, and the two Z formulas agree", () => {
  close(gramPoint(0), 17.845599540535, 1e-10);
  close(theta(gramPoint(100)), 100 * Math.PI, 1e-10);
  for (const t of [450, 1000, 3000]) close(ZEM(t), ZRS(t), 1e-8, `Z(${t})`);
  close(Z(1000), 0.99779463752, 1e-8);
});
test("research: first zeta zeros and N(100) = 29", () => {
  const r = zetaZeros(100);
  eq(r.count, 29); eq(r.rvm.count, 29); ok(r.allOnCriticalLine);
  close(r.zeros[0], 14.134725141734693, 1e-12); close(r.zeros[1], 21.022039638771555, 1e-12); close(r.zeros[2], 25.010857580145688, 1e-12);
  for (let i = 0; i < 10; i++) close(r.zeros[i], KNOWN_ZEROS[i], 1e-11);
});
test("research: zeros up to 1000 and 5000 all certified on the line", () => {
  const a = zetaZeros(1000);
  eq(a.count, 649); eq(a.rvm.count, 649); ok(a.allOnCriticalLine); ok(a.turing.applied && a.turing.agrees);
  const b = zetaZeros(5000);
  eq(b.count, b.rvm.count); ok(b.allOnCriticalLine); ok(b.turing.agrees); eq(b.count, 4520);
});

// ------------------------------------------------------------------ Euler bricks
test("research: Euler bricks up to 1000 (smallest 44, 117, 240), no perfect cuboid", () => {
  const r = eulerBricks(1000);
  eq([r.bricks[0].a, r.bricks[0].b, r.bricks[0].c].join(), "44,117,240");
  const keys = new Set(r.bricks.map((b) => `${b.a},${b.b},${b.c}`));
  for (const k of ["85,132,720", "140,480,693", "160,231,792", "240,252,275"]) ok(keys.has(k), k);
  eq(r.perfectCuboids.length, 0);
});
test("research: Euler bricks agree with a brute-force triple loop to 700", () => {
  const bf = eulerBricksBrute(700).map((x) => x.join(",")).sort();
  eq(eulerBricks(700).bricks.map((b) => `${b.a},${b.b},${b.c}`).sort().join(";"), bf.join(";"));
});

// ------------------------------------------------------------------ moving sofa
test("research: moving sofa areas and Gerver's parameters", () => {
  const r = movingSofa();
  close(r.semicircle.value, Math.PI / 2, 1e-15);
  close(r.hammersley.value, 2.207416099162478, 1e-14); close(r.hammersley.numeric, r.hammersley.value, 1e-13);
  eq(r.gerver.value, "2.21953166887197");
  const g = gerverParameters();
  close(g.A, 0.094426560843653, 1e-11); close(g.B, 1.399203727333547, 1e-11); close(g.phi, 0.039177364790084, 1e-11); close(g.theta, 0.681301509382725, 1e-11);
  ok(/claimed proof/.test(r.status) && /under review/.test(r.status));
  ok(!/\b(accepted|rejected|refuted)\b/i.test(text(r)));
});

// ------------------------------------------------------------------ recognition
test("research: English and command recognition", () => {
  const cases = [
    ["collatz 27", "collatz", (a) => a.n === 27n], ["collatz(27)", "collatz", (a) => a.n === 27n], ["Collatz 2^100+1", "collatz", (a) => a.n === 2n ** 100n + 1n],
    ["verify collatz up to 1000000", "collatzVerify", (a) => a.N === 1000000n], ["verify the collatz conjecture up to 10^7", "collatzVerify", (a) => a.N === 10n ** 7n],
    ["goldbach 1000000", "goldbach", (a) => a.n === 1000000n], ["verify goldbach up to 10^6", "goldbachVerify", (a) => a.N === 10n ** 6n],
    ["check goldbach's conjecture up to 1e7", "goldbachVerify", (a) => a.N === 10n ** 7n],
    ["twin primes up to 10^6", "twinPrimes", (a) => a.N === 10n ** 6n], ["how many twin primes below 5 million", "twinPrimes", (a) => a.N === 5000000n],
    ["prime gaps up to 10^6", "primeGaps", (a) => a.N === 10n ** 6n],
    ["kaprekar 5", "kaprekar", (a) => a.digits === 5], ["kaprekar 5 digits", "kaprekar", (a) => a.digits === 5], ["Kaprekar routine for 6-digit numbers", "kaprekar", (a) => a.digits === 6],
    ["kaprekar 4 digits base 8", "kaprekar", (a) => a.digits === 4 && a.base === 8], ["6174", "kaprekar", (a) => a.digits === 4],
    ["riemann zeros up to 100", "zetaZeros", (a) => a.T === 100], ["zeta zeros 50", "zetaZeros", (a) => a.T === 50], ["first 20 zeta zeros", "zetaZeros", (a) => a.count === 20],
    ["zeros of the riemann zeta function up to 1000", "zetaZeros", (a) => a.T === 1000],
    ["zeta(2)", "zeta", (a) => a.re === 2 && a.im === 0], ["zeta(0.5 + 14.1347i)", "zeta", (a) => a.re === 0.5 && Math.abs(a.im - 14.1347) < 1e-12],
    ["euler bricks up to 1000", "eulerBricks", (a) => a.maxEdge === 1000n], ["perfect cuboid", "eulerBricks", () => true], ["moving sofa", "sofa", () => true], ["the sofa problem", "sofa", () => true],
    ["riemann hypothesis", "card", (a) => a.id === "riemann" && !a.askedForProof], ["p vs np", "card", (a) => a.id === "pvsnp"], ["Is P = NP?", "card", (a) => a.id === "pvsnp"],
    ["navier stokes", "card", (a) => a.id === "navierstokes"], ["hodge conjecture", "card", (a) => a.id === "hodge"], ["yang mills", "card", (a) => a.id === "yangmills"],
    ["birch swinnerton-dyer", "card", (a) => a.id === "bsd"], ["poincare conjecture", "card", (a) => a.id === "poincare"], ["millennium problems", "card", (a) => a.id === "millennium"],
    ["solve the riemann hypothesis", "card", (a) => a.id === "riemann" && a.askedForProof], ["prove the riemann hypothesis", "card", (a) => a.id === "riemann" && a.askedForProof],
    ["prove that P != NP", "card", (a) => a.id === "pvsnp" && a.askedForProof], ["solve the collatz conjecture", "card", (a) => a.id === "collatz" && a.askedForProof],
    ["twin prime conjecture", "card", (a) => a.id === "twinprimes"], ["what is the goldbach conjecture", "card", (a) => a.id === "goldbach"],
  ];
  for (const [src, cmd, pred] of cases) {
    const r = recogniseResearch(src);
    ok(r, `not recognised: ${src}`);
    eq(r.command, cmd, src);
    ok(pred(r.args), `args for "${src}": ${text(r.args)}`);
    ok(r.label && r.label.length > 3, `label for ${src}`);
  }
  for (const src of ["x^2 + 3 = 7", "solve x^2 = 4", "derivative of sin x", "factor 360", "2 + 2", ""]) eq(recogniseResearch(src), null, src);
});
test("research: integer text parsing", () => {
  eq(parseIntText("10^6"), 1000000n); eq(parseIntText("1e6"), 1000000n); eq(parseIntText("1,000,000"), 1000000n);
  eq(parseIntText("5 million"), 5000000n); eq(parseIntText("3*10^5"), 300000n); eq(parseIntText("2^64 - 1"), 2n ** 64n - 1n);
  eq(parseIntText("2^^3"), null); eq(parseIntText("abc"), null);
});

// ------------------------------------------------------------------ results and honesty
const HONEST_BAD = /\b(the (riemann hypothesis|conjecture|hypothesis) is (true|false|proved|proven|solved)|quelvra (has )?(proved|proves|solved|solves))\b/i;
test("research: prove the riemann hypothesis yields the honest card", () => {
  const r = solveResearch("prove the riemann hypothesis");
  ok(r.ok); eq(r.solutionStatus, "open-problem"); eq(r.classification.kind, "research");
  const honest = r.answers[0].text;
  ok(/No proof of the Riemann hypothesis is known/.test(honest)); ok(/will not invent a proof/.test(honest));
  ok(r.extra.card.whatQuelvraCanCompute.some((w) => /riemann zeros/.test(w.command || "")));
  eq(honestyViolations(text(r.answers)).length, 0);
});
test("research: no card claims a proof of an open problem", () => {
  for (const card of Object.values(CARDS)) {
    for (const f of ["id", "title", "statement", "status", "whatIsKnown", "whyHard", "whatQuelvraCanCompute", "prize"]) ok(card[f] !== undefined, `${card.id}.${f}`);
    if (!card.open) continue;
    eq(honestyViolations(cardText(card)).join(" | "), "", card.id);
    ok(!HONEST_BAD.test(cardText(card)), card.id);
    // the status line may mention "proved" only historically (with a year), e.g. Helfgott 2013 for weak Goldbach
    if (/\b(proved|solved)\b/i.test(card.status)) ok(/\b(19|20)\d\d\b/.test(card.status), `${card.id} status`);
    ok(/open|conjectured|under review/i.test(card.status), `${card.id} status says open`);
  }
  ok(/Helfgott/.test(CARDS.goldbach.status)); ok(/246/.test(CARDS.twinprimes.whatIsKnown.join(" ")));
  ok(/claimed proof/.test(CARDS.sofa.status) && !/\b(accepted|rejected)\b/i.test(cardText(CARDS.sofa)));
  // the checker itself catches a dishonest sentence
  ok(honestyViolations("Quelvra proved the Riemann hypothesis.").length === 1);
  ok(honestyViolations("Helfgott proved the weak conjecture in 2013.").length === 0);
});
test("research: every command result is honest and independently verified", () => {
  const runs = [["collatz", { n: 27n }], ["collatzVerify", { N: 100000 }], ["goldbach", { n: 1000000n }], ["goldbachVerify", { N: 100000 }],
    ["twinPrimes", { N: 100000 }], ["primeGaps", { N: 100000 }], ["zetaZeros", { T: 200 }], ["zetaZeros", { count: 15 }], ["zeta", { re: 2, im: 0 }],
    ["eulerBricks", { maxEdge: 2000 }], ["sofa", {}], ...Object.keys(CARDS).map((id) => ["card", { id, askedForProof: true }]), ["kaprekar", { digits: 5 }]];
  for (const [cmd, args] of runs) {
    const r = runResearch(cmd, args);
    ok(r.ok, `${cmd} ok`); eq(r.classification.kind, "research");
    ok(["exact", "evidence", "open-problem", "approximate", "info", "partial"].includes(r.solutionStatus), `${cmd} status ${r.solutionStatus}`);
    ok(r.verification.status === "passed" || r.verification.status === "not-applicable", `${cmd} verification ${r.verification.status}: ${text(r.verification.checks.filter((c) => !c.passed))}`);
    if (!["card", "zeta"].includes(cmd)) ok(r.verification.checks.length >= 1, `${cmd} has checks`);
    const t = text({ answers: r.answers, steps: r.steps, card: r.extra && r.extra.card });
    ok(!HONEST_BAD.test(t), `${cmd}: ${t.match(HONEST_BAD)}`);
    // Kaprekar is a finite, fully decided question, so "proved by exhaustive computation" is correct there
    const finite = cmd === "kaprekar" || (cmd === "card" && !CARDS[args.id].open && args.id === "kaprekar");
    if (!finite) eq(honestyViolations(t).join(" | "), "", `${cmd} ${args.id || ""}`);
    if (r.solutionStatus === "evidence") ok(r.answers.some((a) => a.kind === "evidence" && /Evidence, not a proof/.test(a.text) && /open/.test(a.text)), `${cmd} evidence label`);
  }
  const k = runResearch("kaprekar", { digits: 4 });
  eq(k.solutionStatus, "exact"); ok(/proved by exhaustive computation/.test(k.answers.map((a) => a.text).join(" ")));
  eq(runResearch("zetaZeros", { count: 15 }).answers.filter((a) => a.kind === "approx").length, 10);
});
test("research: bounds and budgets fail loudly instead of hanging", () => {
  const a = runResearch("zetaZeros", { T: 1e9 }); eq(a.ok, false); ok(/capped/.test(a.answers[0].label));
  const b = runResearch("goldbachVerify", { N: 10n ** 12n }); eq(b.ok, false);
  const c = runResearch("collatzVerify", { N: 10 ** 9 }, { timeMs: 50 }); eq(c.ok, false); ok(/Time limit/.test(c.answers[0].label));
  const d = runResearch("nonsense", {}); eq(d.ok, false);
  const e = runResearch("goldbach", { n: 9 }); eq(e.ok, false); eq(e.solutionStatus, "unsupported");
});
test("research: default bounds finish quickly", () => {
  for (const [cmd, args] of [["kaprekar", { digits: DEFAULTS.kaprekar }], ["collatzVerify", {}], ["goldbachVerify", {}], ["twinPrimes", {}], ["zetaZeros", {}], ["eulerBricks", {}]]) {
    const t = performance.now(); const r = runResearch(cmd, args); const ms = performance.now() - t;
    ok(r.ok, cmd); ok(ms < 3000, `${cmd} took ${ms.toFixed(0)} ms`);
  }
});
test("research: orchestrator strategy is registered and runs parsed calls", () => {
  const s = strategies().find((x) => x.id === "research");
  ok(s); ok(s.kinds.includes("command"));
  ok(s.applies({ command: "collatz" })); ok(!s.applies({ command: "det" }));
  const c = s.run(X.fn("collatz", X.num(27)), { command: "collatz" }, { deadline: performance.now() + 5000 });
  eq(c.answers[0].text, "111"); eq(c.solutionStatus, "exact"); eq(c.verify().status, "passed");
  const z = s.run(X.fn("zetazeros", X.num(50)), { command: "zetazeros" }, { deadline: performance.now() + 5000 });
  eq(z.solutionStatus, "evidence");
});
