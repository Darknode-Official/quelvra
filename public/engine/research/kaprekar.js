// Quelvra research lab: complete classification of the Kaprekar routine for a fixed digit count.
//
// K(x) = (digits of x sorted descending) - (digits sorted ascending), with x written with exactly d
// digits in base b (leading zeros kept, so 0999 is a legitimate 4-digit string). K(x) depends only
// on the MULTISET of digits of x, so the whole dynamical system on b^d strings is determined by the
// C(d+b-1, d) multisets. Iterating over multisets (not numbers) makes 20 decimal digits feasible.
// For a fixed d this is a finite, exhaustively decidable statement: status "proved by exhaustive computation".

import { asBudget, budgetError } from "./budget.js";

export const KAPREKAR_MAX_MULTISETS = 12_000_000;

function binomTable(n) {
  const C = [];
  for (let i = 0; i <= n; i++) { C.push(new Array(n + 1).fill(0)); C[i][0] = 1; for (let j = 1; j <= i; j++) C[i][j] = C[i - 1][j - 1] + C[i - 1][j]; }
  return C;
}
const multisetCount = (d, b) => binomTable(d + b)[d + b - 1][d];

// Colex rank of a multiset given as counts[0..b-1] summing to d: nondecreasing digits a_1..a_d map to
// the strictly increasing combination a_i + i - 1; rank = sum C(a_i + i - 1, i).
function makeRanker(d, b) {
  const C = binomTable(d + b);
  return (counts) => {
    let r = 0, i = 1;
    for (let digit = 0; digit < b; digit++) for (let k = 0; k < counts[digit]; k++, i++) r += C[digit + i - 1][i];
    return r;
  };
}

// Image digits of K for a multiset: descending minus ascending, digit-wise with borrow. Returns counts.
function imageCounts(counts, d, b, desc, out) {
  let k = 0;
  for (let digit = b - 1; digit >= 0; digit--) for (let c = 0; c < counts[digit]; c++) desc[k++] = digit;
  out.fill(0);
  let borrow = 0;
  for (let i = d - 1; i >= 0; i--) {           // position i of desc (most significant first); asc[i] = desc[d-1-i]
    let v = desc[i] - desc[d - 1 - i] - borrow;
    if (v < 0) { v += b; borrow = 1; } else borrow = 0;
    out[v]++;
  }
  return out;
}
// The actual number K(M) as a BigInt (only needed for the few cycle members).
function imageValue(counts, d, b) {
  const desc = [];
  for (let digit = b - 1; digit >= 0; digit--) for (let c = 0; c < counts[digit]; c++) desc.push(digit);
  let hiV = 0n, loV = 0n;
  const B = BigInt(b);
  for (let i = 0; i < d; i++) { hiV = hiV * B + BigInt(desc[i]); loV = loV * B + BigInt(desc[d - 1 - i]); }
  return hiV - loV;
}
export function toDigitsFixed(x, d, b = 10) {
  const B = BigInt(b), out = [];
  let v = BigInt(x);
  for (let i = 0; i < d; i++) { out.push(Number(v % B)); v /= B; }
  return out.reverse();
}
export const formatFixed = (x, d, b = 10) => toDigitsFixed(x, d, b).map((v) => v.toString(b)).join("");

// Direct Kaprekar step on one number (independent code path used for verification and brute force).
export function kaprekarStep(x, d, b = 10) {
  const ds = toDigitsFixed(x, d, b);
  const asc = ds.slice().sort((p, q) => p - q), desc = asc.slice().reverse();
  const B = BigInt(b);
  const val = (a) => a.reduce((s, v) => s * B + BigInt(v), 0n);
  return val(desc) - val(asc);
}

export function kaprekar(digits = 4, base = 10, opts = {}) {
  const d = Number(digits), b = Number(base);
  if (!Number.isInteger(d) || d < 2) throw budgetError("UNSUPPORTED", "Kaprekar routine needs at least 2 digits");
  if (!Number.isInteger(b) || b < 2 || b > 36) throw budgetError("UNSUPPORTED", "base must be an integer from 2 to 36");
  const M = multisetCount(d, b);
  const cap = opts.maxMultisets || KAPREKAR_MAX_MULTISETS;
  if (M > cap) throw budgetError("BUDGET", `${d} digits in base ${b} has ${M} digit multisets; the cap is ${cap}.`);
  const budget = asBudget(opts, "Kaprekar classification");
  const rank = makeRanker(d, b);
  const next = new Int32Array(M);
  const isRep = new Uint8Array(M);
  const countsOf = new Array(M);  // compact storage: counts packed as Uint8Array per multiset only when M is small
  const keep = M <= 400000;
  const cnt = new Uint8Array(b), desc = new Uint8Array(d), img = new Uint8Array(b);
  // Multiplicities: number of fixed-width strings with a given multiset, and of those with a nonzero leading
  // digit. Each multinomial is a product of binomials, exact in a double while it stays below 2^53; totals are
  // accumulated exactly with Acc (a double part flushed into a BigInt).
  const CB = binomTable(d + 1);
  let balanced = 1, rem = d;
  for (let q = 0; q < b; q++) { const c = Math.floor(rem / (b - q)); balanced *= CB[rem][c]; rem -= c; }
  const numeric = balanced < 2 ** 52;
  const allCount = numeric ? new Float64Array(M) : new Array(M);
  const properCount = numeric ? new Float64Array(M) : new Array(M);
  const multinomial = (c, total) => {
    if (numeric) { let m = 1, r2 = total; for (let q = 0; q < b; q++) { m *= CB[r2][c[q]]; r2 -= c[q]; } return m; }
    let m = 1n, r2 = total; for (let q = 0; q < b; q++) { m *= BigInt(CB[r2][c[q]]); r2 -= c[q]; } return m;
  };
  let visited = 0;
  // enumerate all count vectors
  const rec = (digit, left) => {
    if (digit === b - 1) {
      cnt[digit] = left;
      const r = rank(cnt);
      let repd = false;
      for (let q = 0; q < b; q++) if (cnt[q] === d) repd = true;
      isRep[r] = repd ? 1 : 0;
      imageCounts(cnt, d, b, desc, img);
      next[r] = rank(img);
      const all = multinomial(cnt, d);
      let lead0 = numeric ? 0 : 0n;               // strings starting with 0
      if (cnt[0] > 0) { cnt[0]--; lead0 = multinomial(cnt, d - 1); cnt[0]++; }
      allCount[r] = all;
      properCount[r] = all - lead0;
      if (keep) countsOf[r] = Uint8Array.from(cnt);
      visited++;
      budget.tick(d + b);
      if ((visited & 0xffff) === 0) budget.progress(visited / M, "Kaprekar classification");
      return;
    }
    for (let c = left; c >= 0; c--) { cnt[digit] = c; rec(digit + 1, left - c); }
  };
  rec(0, d);
  if (visited !== M) throw new Error("internal: multiset enumeration count mismatch");

  // cycles of the functional graph on multisets
  const state = new Int8Array(M);        // 0 new, 1 on stack, 2 done
  const cycleId = new Int32Array(M).fill(-1);
  const cycles = [];
  const path = [];
  for (let s = 0; s < M; s++) {
    if (state[s]) continue;
    path.length = 0;
    let v = s;
    while (state[v] === 0) { state[v] = 1; path.push(v); v = next[v]; budget.tick(); }
    if (state[v] === 1) {
      const members = [];
      let u = v;
      do { members.push(u); cycleId[u] = cycles.length; u = next[u]; } while (u !== v);
      cycles.push(members);
    }
    for (const w of path) state[w] = 2;
  }
  // steps to reach a cycle NUMBER for a non-cycle number with multiset m: h(m) = 1 + (K(m) on cycle ? 0 : h(next m)).
  // K(m) is a cycle number exactly when next[m] lies on a cycle AND m's image is that cycle's member, i.e. m's image
  // multiset is on a cycle: the unique cycle number with multiset next[m] is K(prev) for the cycle predecessor; K(m)
  // equals it iff ... K(m) is determined by m, and next[m] on a cycle means K(m) has a cycle multiset; the cycle
  // number with that multiset is K(pred) where pred is the cycle predecessor. We compare actual values.
  const cycleNumber = new Map(); // multiset rank (on cycle) -> BigInt number on the cycle with that multiset
  const needCounts = (r) => (keep ? countsOf[r] : unrank(r, d, b));
  for (const members of cycles) {
    for (let i = 0; i < members.length; i++) {
      const pred = members[(i - 1 + members.length) % members.length];
      cycleNumber.set(members[i], imageValue(needCounts(pred), d, b));
    }
  }
  const attractor = new Int32Array(M).fill(-1);
  const h = new Int32Array(M).fill(-1);
  const stack = [];
  for (let s = 0; s < M; s++) {
    if (h[s] >= 0) continue;
    let v = s;
    stack.length = 0;
    while (h[v] < 0 && cycleId[v] < 0) { stack.push(v); v = next[v]; budget.tick(); }
    // v is either resolved or on a cycle
    if (cycleId[v] >= 0 && h[v] < 0) {
      // members of a cycle: their non-cycle numbers step once onto a cycle number? only if K(m) is the cycle number
      for (const u of cycles[cycleId[v]]) { attractor[u] = cycleId[v]; h[u] = 1; }
    }
    for (let i = stack.length - 1; i >= 0; i--) {
      const u = stack[i], w = next[u];
      attractor[u] = attractor[w];
      // K(u) has multiset w. It is a cycle number iff w is on a cycle and K(u) equals that cycle number.
      let onCycleNumber = false;
      if (cycleId[w] >= 0) onCycleNumber = imageValue(needCounts(u), d, b) === cycleNumber.get(w);
      h[u] = 1 + (onCycleNumber ? 0 : h[w]);
    }
  }
  // cycle members: numbers with a cycle multiset that are not the cycle number itself map to K(m) = cycle number
  // of the successor, which is on the cycle, so h = 1 (set above). The cycle number itself has 0 steps.

  const res = cycles.map((members) => {
    const nums = members.map((r) => cycleNumber.get(r));
    let start = 0;
    for (let i = 1; i < nums.length; i++) if (nums[i] > nums[start]) start = i;
    const ordered = [];
    for (let i = 0; i < nums.length; i++) ordered.push(nums[(start + i) % nums.length]);
    return { members: ordered, length: members.length, all: new Acc(), proper: new Acc(), maxSteps: 0, isZero: ordered.length === 1 && ordered[0] === 0n };
  });
  let maxSteps = 0, maxStepsExample = null;
  const hist = new Map();
  const H = (k) => { let v = hist.get(k); if (!v) hist.set(k, (v = new Acc())); return v; };
  const repAll = new Acc(), repProper = new Acc(), totalAll = new Acc(), totalProper = new Acc();
  for (let r = 0; r < M; r++) {
    const ac = allCount[r], pc = properCount[r];
    totalAll.add(ac); totalProper.add(pc);
    if (isRep[r]) { repAll.add(ac); repProper.add(pc); continue; }
    const a = res[attractor[r]];
    a.all.add(ac); a.proper.add(pc);
    let nonCyc = ac;
    if (cycleId[r] >= 0) { nonCyc = numeric ? ac - 1 : ac - 1n; H(0).add(numeric ? 1 : 1n); }
    if (numeric ? nonCyc > 0 : nonCyc > 0n) {
      H(h[r]).add(nonCyc);
      if (h[r] > a.maxSteps) a.maxSteps = h[r];
      if (h[r] > maxSteps) { maxSteps = h[r]; maxStepsExample = r; }
    }
    if ((r & 0xfffff) === 0) budget.tick(1);
  }
  for (const a of res) {
    a.basinAll = a.all.value(); a.basinProper = a.proper.value(); delete a.all; delete a.proper;
    a.membersText = a.members.map((x) => formatFixed(x, d, b));
    a.type = a.length === 1 ? "fixed point" : `cycle of length ${a.length}`;
  }
  // an example starting number achieving maxSteps: smallest number with that multiset whose leading digit is nonzero
  let example = null;
  if (maxStepsExample !== null) {
    const c = needCounts(maxStepsExample);
    const ds = [];
    for (let q = 0; q < b; q++) for (let k = 0; k < c[q]; k++) ds.push(q);
    const nz = ds.findIndex((v) => v > 0);
    if (nz > 0) { const [v] = ds.splice(nz, 1); ds.unshift(v); }
    example = ds.reduce((s, v) => s * BigInt(b) + BigInt(v), 0n);
    if (cycleId[maxStepsExample] >= 0 && example === cycleNumber.get(maxStepsExample)) example = null;
  }
  const nonTrivial = res.filter((a) => !a.isZero && a.basinAll > 0n);
  const zeroAttr = res.find((a) => a.isZero);
  const fixedPoints = nonTrivial.filter((a) => a.length === 1).map((a) => a.members[0]);
  const cyc = nonTrivial.filter((a) => a.length > 1);
  return {
    digits: d, base: b, multisets: M, totalAll: totalAll.value(), totalProper: totalProper.value(),
    repdigits: { all: repAll.value(), proper: repProper.value(), note: `Repdigits (all ${d} digits equal) map to 0 and are excluded.` },
    zeroBasin: zeroAttr ? { all: zeroAttr.basinAll, proper: zeroAttr.basinProper, note: "non-repdigit strings that reach 0" } : null,
    attractors: nonTrivial.sort((p, q) => p.length - q.length || (p.members[0] < q.members[0] ? -1 : 1)),
    fixedPoints, cycles: cyc,
    maxSteps, maxStepsExample: example,
    stepHistogram: [...hist.entries()].sort((p, q) => p[0] - q[0]).map(([steps, count]) => ({ steps, count: count.value() })),
    status: "proved by exhaustive computation",
    convention: `every ${d}-digit string in base ${b} is used, with leading zeros kept (fixed width). basinProper counts only strings with a nonzero leading digit; basinAll counts all ${b}^${d} strings.`,
    ms: budget.elapsed(),
  };
}

// Exact accumulator: doubles below 2^52 are summed natively and flushed into a BigInt.
class Acc {
  constructor() { this.hi = 0n; this.lo = 0; }
  add(x) {
    if (typeof x === "bigint") { this.hi += x; return; }
    this.lo += x;
    if (this.lo > 4e15) { this.hi += BigInt(this.lo); this.lo = 0; }
  }
  value() { return this.hi + BigInt(this.lo); }
}

// Recover a multiset from its colex rank (used when counts are not cached).
function unrank(r, d, b) {
  const C = binomTable(d + b);
  const out = new Uint8Array(b);
  let x = r;
  for (let i = d; i >= 1; i--) {
    let c = i - 1;
    while (C[c + 1][i] <= x) c++;
    x -= C[c][i];
    out[c - (i - 1)]++;
  }
  return out;
}

// Brute force over all b^d strings (for tests / small d only): returns the set of cycles as sorted member lists.
export function kaprekarBrute(d, b = 10) {
  const total = b ** d;
  if (total > 2e6) throw budgetError("BUDGET", "brute force limited to 2e6 strings");
  const nxt = new Float64Array(total);
  for (let x = 0; x < total; x++) nxt[x] = Number(kaprekarStep(x, d, b));
  const seen = new Set(), cycles = [];
  const color = new Uint8Array(total);
  for (let s = 0; s < total; s++) {
    if (color[s]) continue;
    const path = [];
    let v = s;
    while (!color[v]) { color[v] = 1; path.push(v); v = nxt[v]; }
    if (color[v] === 1) {
      const mem = []; let u = v;
      do { mem.push(u); u = nxt[u]; } while (u !== v);
      const key = mem.slice().sort((p, q) => p - q).join(",");
      if (!seen.has(key)) { seen.add(key); cycles.push(mem.slice().sort((p, q) => p - q)); }
    }
    for (const w of path) color[w] = 2;
  }
  return cycles;
}
