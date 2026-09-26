import { test, eq, ok } from "./harness.js";
import "../public/engine/strategies/basic.js";
import { solve, register } from "../public/engine/orchestrate.js";
import { explain } from "../public/engine/explain.js";
import { toText } from "../public/engine/print.js";
import * as X from "../public/engine/expr.js";

const ans = (s) => { const r = solve(s); return r.answers.filter((a) => a.tree).map((a) => toText(a.tree)).join("; "); };
test("arithmetic exact", () => eq(ans("1/3+1/6"), "1/2"));
test("radicals", () => eq(ans("sqrt(8)+sqrt(2)"), "3sqrt(2)"));
test("simplify prefers expanded when shorter", () => eq(ans("(x+1)^2 - x^2"), "2x + 1"));
test("derivative", () => eq(ans("d/dx x^3"), "3x^2"));
test("derivative from English", () => { const r = solve("derivative of x^3"); eq(r.recognition.source, "language"); eq(toText(r.answers[0].tree), "3x^2"); });
test("four separate confidences", () => { const c = solve("1+1").confidence; ok(["recognition", "classification", "solution", "verification"].every((k) => k in c)); });
test("syntax error has position", () => { const r = solve("(x+1"); ok(!r.ok && r.error.pos >= 0); });
test("refuses English it cannot read", () => { const r = solve("tell me a joke"); ok(!r.ok); ok(/does not understand/.test(r.error.message)); });
test("undefined value is reported, not faked", () => { const r = solve("1/0"); eq(r.answers[0].kind, "none"); });
test("a wrong strategy answer is never reported", () => {
  register({ id: "test.liar", kinds: ["arithmetic"], priority: 1, applies: (c) => c.goal === "evaluate",
    run: (node) => (toText(node) === "2 + 2" ? { answers: [{ kind: "exact", tree: X.num(5) }], solutionStatus: "exact",
      verify: () => ({ status: "failed", checks: [{ name: "re-evaluate", passed: false, detail: "2 + 2 is not 5" }] }) } : null) });
  const r = solve("2+2");
  eq(toText(r.answers[0].tree), "4");
  ok(r.attempts.some((a) => a.strategy === "test.liar" && a.status === "failed"));
});
test("explain teach mode has sections", () => { const e = explain(solve("d/dx sin(x^2)"), "teach"); ok(e.teach && e.steps.length > 0 && e.teach.concepts.length > 0); });
test("attempts record timing", () => ok(solve("2^100").attempts.every((a) => typeof a.ms === "number")));
