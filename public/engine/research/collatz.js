// Quelvra research lab: the Collatz (3n + 1) map.
//
// collatz(n): the trajectory of one starting value (any size, BigInt).
// collatzVerify(N): checks that EVERY n <= N reaches 1. The conjecture itself remains open; this is a
// bounded verification (it has been verified by others far beyond anything a browser can reach).

import { asBudget, toBigIntArg, budgetError } from "./budget.js";

export const COLLATZ_VERIFY_MAX = 2e9;
const MEMO_MAX = 1 << 25;                 // step-count memo size cap (Uint16, 64 MB at most)
const SAFE = Math.floor((Number.MAX_SAFE_INTEGER - 1) / 3);

// Single trajectory. opts.pathCap limits the stored path (default 1000 values).
export function collatz(n, opts = {}) {
  const budget = asBudget(opts, "Collatz trajectory");
  let x = toBigIntArg(n, "n");
  if (x < 1n) throw budgetError("UNSUPPORTED", "the Collatz map is studied on positive integers (n >= 1)");
  const start = x;
  const cap = opts.pathCap ?? 1000;
  const path = [x];
  let steps = 0, odd = 0, peak = x, peakAt = 0, stoppingTime = null;
  const maxSteps = opts.maxSteps ?? 1e7;
  while (x !== 1n) {
    if (x & 1n) { x = 3n * x + 1n; odd++; } else x >>= 1n;
    steps++;
    if (x > peak) { peak = x; peakAt = steps; }
    if (stoppingTime === null && x < start) stoppingTime = steps;
    if (path.length < cap) path.push(x);
    budget.tick(1 + (x.toString(16).length >> 4));
    if (steps > maxSteps) throw budgetError("BUDGET", `no arrival at 1 within ${maxSteps} steps (raise maxSteps); this is NOT evidence against the conjecture by itself`);
  }
  return { n: start, steps, oddSteps: odd, evenSteps: steps - odd, peak, peakAt, stoppingTime: start === 1n ? 0 : stoppingTime, path, pathTruncated: steps + 1 > path.length, reachedOne: true, ms: budget.elapsed() };
}

// Verify every 1 <= n <= N reaches 1. Each n is iterated only until it drops below n (all smaller values are
// already verified); total step counts come from a memo. Values that could overflow 2^53 switch to BigInt.
export function collatzVerify(N = 1000000, opts = {}) {
  const budget = asBudget(opts, "Collatz verification");
  const n0 = Number(toBigIntArg(N, "N"));
  if (n0 < 1) throw budgetError("UNSUPPORTED", "N must be at least 1");
  if (n0 > COLLATZ_VERIFY_MAX) throw budgetError("BUDGET", `N is capped at ${COLLATZ_VERIFY_MAX}.`);
  const memoN = Math.min(n0 + 1, MEMO_MAX);
  const memo = new Uint16Array(memoN);   // total steps to reach 1 (max for n < 2^31 is well below 65535)
  const stepsLong = new Map();           // spill-over for step counts that do not fit (never expected)
  memo[1] = 0;
  let longest = { n: 1, steps: 0 }, highest = { n: 1, peak: 1 };
  const stepRecords = [{ n: 1, steps: 0 }], peakRecords = [{ n: 1, peak: 1 }];
  let bigintUsed = 0, totalIter = 0;
  const stepsOf = (v) => (v < memoN ? memo[v] : null);
  for (let n = 2; n <= n0; n++) {
    let x = n, k = 0, segMax = n, total;
    // iterate until x < n (then its total is known) — x < memoN is guaranteed once x < n <= n0 < memoN,
    // otherwise (n > memo size) iterate until x < memoN.
    const limit = n < memoN ? n : memoN;
    while (x >= limit) {
      if (x & 1) {
        if (x > SAFE) { const r = bigTail(BigInt(x), limit, budget); k += r.k; if (r.max > segMax) segMax = r.max; x = r.x; bigintUsed++; break; }
        x = 3 * x + 1; if (x > segMax) segMax = x;
        x /= 2; k += 2;                     // 3x + 1 is even: take both steps
      } else { x /= 2; k++; }
    }
    totalIter += k;
    const tail = stepsOf(x);
    total = k + (tail === 65535 ? stepsLong.get(x) : tail);
    if (n < memoN) { if (total >= 65535) { memo[n] = 65535; stepsLong.set(n, total); } else memo[n] = total; }
    if (total > longest.steps) { longest = { n, steps: total }; stepRecords.push(longest); }
    // peak(n) = max(segMax, peak(x)) and peak(x) <= current peak record, so segMax decides records exactly
    if (segMax > highest.peak) { highest = { n, peak: segMax }; peakRecords.push(highest); }
    if ((n & 0xffff) === 0) { budget.tick(k + 65536); budget.progress(n / n0, "Collatz verification"); }
  }
  return {
    N: n0, allReachOne: true, longest, highest, stepRecords, peakRecords, bigintSwitches: bigintUsed,
    averageStepsToDropBelowStart: n0 > 1 ? totalIter / (n0 - 1) : 0,
    method: "iterate each n until it drops below n (all smaller values already verified); memoised total stopping times",
    status: "verified for all n <= N; the conjecture remains open (verified by others far beyond this bound)",
    ms: budget.elapsed(),
  };
}
function bigTail(x, limit, budget) {
  const L = BigInt(limit);
  let k = 0, max = Number(x);
  while (x >= L) {
    if (x & 1n) x = 3n * x + 1n; else x >>= 1n;
    k++;
    const f = Number(x); if (f > max) max = f;
    budget.tick(4);
  }
  return { x: Number(x), k, max };
}
