// Everyday wording: every case must be understood, verified and correct (no refusal, no wrong answer).
import { test, eq } from "./harness.js";
import { solve } from "../public/engine/quelvra.js";
import { judge, textOf } from "../tools/coverage-judge.mjs";
import { CASES } from "../tools/everyday-cases.mjs";

test("everyday phrasings: all answered, verified and correct", () => {
  const bad = [];
  for (const [area, input, exp] of CASES) {
    let r, v;
    try { r = solve(input, { timeLimit: 5000 }); v = judge(exp, r); } catch (e) { v = "crash " + e.message; r = { answers: [] }; }
    if (v !== "ok") bad.push(`[${area}] ${input} -> ${v}: ${(r.answers || []).map(textOf).join("; ")}`);
  }
  eq(bad.length, 0, bad.join("\n"));
});
