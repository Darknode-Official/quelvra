// Minimal test harness for Quelvra (no dependencies).
import { parse } from "../public/engine/parse.js";
import { simplify } from "../public/engine/simplify.js";
import { toText } from "../public/engine/print.js";

export const TESTS = [];
let currentFile = "";
export const setFile = (f) => { currentFile = f; };
export function test(name, fn) { TESTS.push({ file: currentFile, name, fn }); }

export class AssertionError extends Error {}
export function ok(cond, msg = "assertion failed") { if (!cond) throw new AssertionError(msg); }
export function eq(actual, expected, msg = "") {
  if (actual !== expected) throw new AssertionError(`${msg ? msg + ": " : ""}expected ${JSON.stringify(expected)}, got ${JSON.stringify(actual)}`);
}
export function throws(fn, msg = "expected an error") {
  try { fn(); } catch (_) { return; }
  throw new AssertionError(msg);
}
export async function rejects(p, msg = "expected rejection") {
  try { await p; } catch (_) { return; }
  throw new AssertionError(msg);
}
export function close(a, b, tol = 1e-9, msg = "") {
  if (!(Math.abs(a - b) <= tol * Math.max(1, Math.abs(b)))) throw new AssertionError(`${msg ? msg + ": " : ""}expected ~${b}, got ${a}`);
}
// parse + simplify + print
export const P = (s) => simplify(parse(s));
export const T = (s) => toText(simplify(parse(s)));

// Deterministic PRNG (mulberry32) for property tests.
export function rng(seed = 12345) {
  let a = seed >>> 0;
  const next = () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
  return {
    next,
    int: (lo, hi) => lo + Math.floor(next() * (hi - lo + 1)),
    pick: (arr) => arr[Math.floor(next() * arr.length)],
  };
}
