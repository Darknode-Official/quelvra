// Quelvra coverage probe: typical student/competition problems across areas.
//   node tools/coverage.mjs [area] [-v] [--heldout]
// Each case: [area, input, expectation]. Expectations:
//   number            one answer numerically equal (exact tree or approx)
//   {roots:[...]}     the set of real solutions, numerically
//   {expr:"...", v}   an answer equivalent to the expression (by sampling v)
//   {anti:"...", v}   an antiderivative equal up to a constant
//   {re:/.../}        answer text matches
//   {refuse:true}     must not answer
// Verdicts: ok (verified and correct), refused (no verified answer), WRONG (verified but not correct).
import { solve } from "../public/engine/quelvra.js";
import { judge, textOf } from "./coverage-judge.mjs";
import { CASES as MAIN } from "./coverage-cases.mjs";
import { CASES as HELDOUT } from "./coverage-heldout.mjs";

const args = process.argv.slice(2);
const verbose = args.includes("-v");
const filter = args.find((a) => !a.startsWith("-"));
const CASES = args.includes("--heldout") ? HELDOUT : MAIN;

const byArea = new Map();
const rows = [];
for (const [area, input, exp] of CASES) {
  if (filter && area !== filter) continue;
  let v, r = null;
  try { r = solve(input, { timeLimit: 5000 }); v = judge(exp, r); } catch (e) { v = "refused"; r = { error: { message: "CRASH " + e.message } }; }
  const c = byArea.get(area) || { ok: 0, refused: 0, WRONG: 0, total: 0 };
  c[v] = (c[v] || 0) + 1; c.total++;
  byArea.set(area, c);
  const shown = r && r.answers ? r.answers.map(textOf).join("; ").slice(0, 120) : "";
  const why = r && r.error ? r.error.message : "";
  rows.push([v, area, input, shown || why]);
  if (verbose || v !== "ok") console.log(`${v.padEnd(7)} [${area}] ${input}  ->  ${(shown || why || "").slice(0, 140)}`);
}
console.log("");
let T = { ok: 0, refused: 0, WRONG: 0, total: 0 };
for (const [a, c] of byArea) { console.log(`${a.padEnd(12)} ok ${String(c.ok).padStart(3)}  refused ${String(c.refused).padStart(3)}  WRONG ${String(c.WRONG || 0).padStart(2)}  / ${c.total}`); for (const k in T) T[k] += c[k] || 0; }
console.log(`${"TOTAL".padEnd(12)} ok ${T.ok}  refused ${T.refused}  WRONG ${T.WRONG}  / ${T.total}`);
