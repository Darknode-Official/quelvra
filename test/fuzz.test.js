// Property / metamorphic fuzzing (fixed seed, small, no oracle): tools/quelvra-fuzz-lib.mjs.
// The large differential run with the sympy/mpmath oracle is `node tools/quelvra-fuzz.mjs`.
// Every check here is independent of the engine's own verifier: the generator's AST is evaluated
// by its own evaluator, answers by an evaluator of Quelvra trees that does not use verify.js.
import { test, ok } from "./harness.js";
import { generate, runCase, checkParse, checkSubstitution, checkEqTruth, answerKey } from "../tools/fuzz-lib.mjs";
import { solve } from "../public/engine/quelvra.js";

const SEED = 20260926;
const PLAN = { parse: 150, "eq-poly": 60, "eq-rational": 24, "eq-radical": 24, "eq-exp": 18, "eq-log": 18, "eq-trig": 15, "eq-abs": 18, ineq: 15, "sys-linear": 10, diff: 10, anti: 8 };

for (const [cat, n] of Object.entries(PLAN)) {
  test(`fuzz ${cat}: ${n} seeded cases, no verified answer fails an independent check`, () => {
    const cases = generate(cat, n, SEED);
    const bad = [];
    const keys = new Map();
    for (const c of cases) {
      if (cat === "parse") {
        for (const p of checkParse(c)) bad.push(`${c.input}: ${p.detail}`);
        continue;
      }
      let r;
      try { r = solve(c.input, { timeLimit: 8000 }); } catch (e) { bad.push(`${c.input}: crash ${e.message}`); continue; }
      const probs = [...checkSubstitution(c, r), ...checkEqTruth(c, r)].filter((p) => p.type === "wrong");
      for (const p of probs) bad.push(`${c.input}: ${p.detail}`);
      const k = answerKey(r);
      if (k != null) {
        if (!keys.has(c.group)) keys.set(c.group, new Map());
        keys.get(c.group).set(c.input, k);
      }
    }
    // metamorphic: every verified variant of one problem has the same answer set
    for (const [g, m] of keys) if (new Set(m.values()).size > 1) bad.push(`group ${g} disagrees: ${[...m].map(([i, k]) => `${i} -> ${k}`).join(" | ")}`);
    ok(!bad.length, bad.slice(0, 5).join("\n     "));
  });
}

test("fuzz harness: runCase reports timing and never throws", () => {
  const c = runCase("x^2 - 1 = 0");
  ok(c.verified && c.ms >= 0 && c.answers.length === 2, JSON.stringify(c.answers));
});
