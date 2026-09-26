// Quelvra research lab: Euler bricks and the perfect cuboid problem.
//
// An Euler brick has integer edges a < b < c whose three face diagonals sqrt(a^2+b^2), sqrt(a^2+c^2),
// sqrt(b^2+c^2) are all integers. A perfect cuboid is an Euler brick whose space diagonal
// sqrt(a^2+b^2+c^2) is also an integer. None is known and none has been ruled out: the problem is open.
// This module enumerates ALL Euler bricks with largest edge <= L (exact integer arithmetic), so
// "no perfect cuboid with largest edge <= L" is an exhaustive finite result, and evidence for the conjecture.

import { asBudget, toBigIntArg, budgetError } from "./budget.js";

export const BRICK_MAX_EDGE = 3e7;   // keeps a^2 + b^2 + c^2 < 2^53 with a wide margin
const gcd = (a, b) => { while (b) [a, b] = [b, a % b]; return a; };
export const isSquareNum = (n) => { const r = Math.round(Math.sqrt(n)); return r * r === n ? r : -1; };
export function isqrtBig(n) { if (n < 2n) return n; let x = BigInt(Math.floor(Math.sqrt(Number(n)))); while (x * x > n) x--; while ((x + 1n) * (x + 1n) <= n) x++; return x; }

export function eulerBricks(maxEdge = 10000, opts = {}) {
  const budget = asBudget(opts, "Euler brick search");
  const L = Number(toBigIntArg(maxEdge, "maxEdge"));
  if (L < 1) throw budgetError("UNSUPPORTED", "maxEdge must be positive");
  if (L > BRICK_MAX_EDGE) throw budgetError("BUDGET", `maxEdge is capped at ${BRICK_MAX_EDGE}`);
  // adjacency: legs x -> list of y with x^2 + y^2 a perfect square (both <= L), via Euclid's formula
  const adj = new Map();
  const link = (x, y) => { let a = adj.get(x); if (!a) adj.set(x, (a = [])); a.push(y); };
  let pairs = 0;
  // both legs <= L forces m^2 <= L (1 + sqrt 2) / 2 + 1, and for each m: k <= L / (2m), k^2 >= m^2 - L
  const mMax = Math.ceil(Math.sqrt(L * (1 + Math.SQRT2) / 2)) + 2;
  for (let m = 2; m <= mMax; m++) {
    const kLo = Math.max(1, Math.ceil(Math.sqrt(Math.max(0, m * m - L))));
    const kHi = Math.min(m - 1, Math.floor(L / (2 * m)));
    for (let k = kLo; k <= kHi; k++) {
      if (((m - k) & 1) === 0 || gcd(m, k) !== 1) continue;   // opposite parity, coprime: primitive triple
      const u = m * m - k * k, v = 2 * m * k;
      if (u > L || v > L) continue;
      for (let s = 1; s * u <= L && s * v <= L; s++) { link(s * u, s * v); link(s * v, s * u); pairs++; }
    }
    budget.tick(kHi - kLo + 2);
  }
  for (const a of adj.values()) a.sort((p, q) => p - q);
  const has = (x, y) => { const a = adj.get(x); if (!a) return false; let lo = 0, hi = a.length - 1; while (lo <= hi) { const mid = (lo + hi) >> 1; if (a[mid] === y) return true; if (a[mid] < y) lo = mid + 1; else hi = mid - 1; } return false; };
  const bricks = [];
  let perfect = [];
  const keys = [...adj.keys()].sort((p, q) => p - q);
  for (const a of keys) {
    const list = adj.get(a);
    let i0 = 0; while (i0 < list.length && list[i0] <= a) i0++;
    for (let i = i0; i < list.length; i++) for (let j = i + 1; j < list.length; j++) {
      const b = list[i], c = list[j];
      budget.tick(1);
      if (!has(b, c)) continue;
      const d = isSquareNum(a * a + b * b + c * c);
      const brick = { a, b, c, dab: isSquareNum(a * a + b * b), dac: isSquareNum(a * a + c * c), dbc: isSquareNum(b * b + c * c), primitive: gcd(gcd(a, b), c) === 1, space: d >= 0 ? d : null, spaceSquared: a * a + b * b + c * c };
      bricks.push(brick);
      if (d >= 0) perfect.push(brick);
    }
  }
  bricks.sort((p, q) => p.c - q.c || p.b - q.b || p.a - q.a);
  // near misses: bricks whose space diagonal is closest to an integer (relative)
  const near = bricks.map((br) => { const r = Math.sqrt(br.spaceSquared); return { ...br, spaceDiagonal: r, offBy: Math.abs(r - Math.round(r)) }; })
    .sort((p, q) => p.offBy - q.offBy).slice(0, 5);
  return {
    maxEdge: L, pythagoreanPairs: pairs, bricks, count: bricks.length, primitiveCount: bricks.filter((b) => b.primitive).length,
    perfectCuboids: perfect, nearMisses: near,
    statement: perfect.length ? "PERFECT CUBOID CANDIDATE FOUND (independent re-check required)" : `no perfect cuboid with largest edge <= ${L}`,
    method: "all Pythagorean leg pairs <= L from Euclid's formula (with multiples); every a < b < c with all three pairs Pythagorean",
    ms: budget.elapsed(),
  };
}

// Brute force (tests only): all a < b < c <= L with the three face diagonals integral.
export function eulerBricksBrute(L) {
  const out = [];
  for (let a = 1; a <= L; a++) for (let b = a + 1; b <= L; b++) {
    if (isSquareNum(a * a + b * b) < 0) continue;
    for (let c = b + 1; c <= L; c++) if (isSquareNum(a * a + c * c) >= 0 && isSquareNum(b * b + c * c) >= 0) out.push([a, b, c]);
  }
  return out;
}
