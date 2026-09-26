// Advanced discrete mathematics: probe corpus (oracle-derived expected values) plus unit tests of
// the certificate checkers. Corpus: advanced-discrete.corpus.json (tools/quelvra-adv-discrete-oracle.py).
import { test, ok, eq } from "./harness.js";
import { CORPUS, judgeCase } from "./advanced-discrete.judge.js";
import "./advanced-discrete-units.js";

const results = new Map();
for (const c of CORPUS) {
  test(`${c.area}: ${c.input}`, () => {
    const v = judgeCase(c);
    results.set(c, v);
    ok(v.cat === "correct", `${v.cat}: ${v.why}`);
  });
}
test("corpus: no wrong answers anywhere", () => {
  const wrong = [...results.entries()].filter(([, v]) => v.cat === "wrong").map(([c, v]) => `${c.input} -> ${v.why}`);
  eq(wrong.length, 0, wrong.join("\n"));
});
