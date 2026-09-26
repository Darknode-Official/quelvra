// Judge for the Quelvra coverage corpora (tools/coverage.mjs, test/coverage.test.js).
// judge(expectation, result) -> "ok" (verified and correct) | "refused" (no verified answer) | "WRONG".
import { toText } from "../public/engine/print.js";
import { parse } from "../public/engine/parse.js";
import { evalC, evalReal } from "../public/engine/verify.js";

const numOf = (a) => {
  try { if (a.tree) { const c = evalC(a.tree, {}, "complex"); if (c && Number.isFinite(c.re) && Math.abs(c.im) < 1e-9 * Math.max(1, Math.abs(c.re))) return c.re; } } catch (_) {}
  if (a.approx && a.approx.value != null) { const v = parseFloat(a.approx.value); if (Number.isFinite(v)) return v; }
  return null;
};
const close = (x, y) => x != null && Math.abs(x - y) <= 1e-7 * Math.max(1, Math.abs(y));
export const textOf = (a) => a.values ? a.values.map(([k, v]) => `${k} = ${toText(v)}`).join(", ") : a.tree ? (a.label ? a.label + " = " : "") + toText(a.tree) + (a.unit ? " " + a.unit : "") : a.approx ? "~" + a.approx.value : (a.text || a.label || a.kind);

function sampleEq(t, want, v) {
  const pts = [0.3, 0.7, 1.3, 2.1, -0.45, 1.7];
  let n = 0;
  for (const p of pts) {
    let a, b;
    try { a = evalReal(t, { [v]: p }); b = evalReal(want, { [v]: p }); } catch (_) { continue; }
    if (!Number.isFinite(a) || !Number.isFinite(b)) continue;
    if (Math.abs(a - b) > 1e-7 * Math.max(1, Math.abs(b))) return false;
    n++;
  }
  return n >= 3;
}
export function judge(exp, r) {
  const answers = (r.answers || []).filter((a) => a.kind !== "none" || a.label);
  const verified = r.verification && r.verification.status === "passed";
  // a verified "diverges" / "no solutions" verdict is an answer too when the expectation is textual
  const real = answers.filter((a) => a.kind !== "none" || (exp && exp.re && a.label));
  if (exp && exp.refuse) return !r.ok || !real.length ? "ok" : "WRONG";
  if (!r.ok || !verified || !real.length) {
    if (r.ok && verified && exp && exp.none && (r.noSolution || answers.some((a) => a.kind === "none"))) return "ok";
    return "refused";
  }
  if (typeof exp === "number") return real.some((a) => close(numOf(a), exp)) ? "ok" : "WRONG";
  if (exp.roots) {
    const got = real.filter((a) => a.kind === "exact" || a.kind === "approx").map(numOf);
    if (got.length !== exp.roots.length || got.some((g) => g == null)) return exp.roots.length === 0 && (r.noSolution) ? "ok" : "WRONG";
    return exp.roots.every((w) => got.some((g) => close(g, w))) ? "ok" : "WRONG";
  }
  if (exp.expr) { const want = parse(exp.expr); return real.some((a) => a.tree && sampleEq(a.tree.k === "eq" ? a.tree.args[1] : a.tree, want, exp.v || "x")) ? "ok" : "WRONG"; }
  if (exp.anti) {
    const want = parse(exp.anti), v = exp.v || "x";
    return real.some((a) => {
      if (!a.tree) return false;
      const d = [0.3, 0.7, 1.3, 2.1].map((p) => { try { return evalReal(a.tree, { [v]: p }) - evalReal(want, { [v]: p }); } catch (_) { return NaN; } });
      return d.every(Number.isFinite) && d.every((x) => Math.abs(x - d[0]) < 1e-7 * Math.max(1, Math.abs(d[0])));
    }) ? "ok" : "WRONG";
  }
  if (exp.re) return real.some((a) => exp.re.test(textOf(a))) || exp.re.test(real.map(textOf).join("; ")) ? "ok" : "WRONG";
  if (exp.none) return r.noSolution || answers.some((a) => a.kind === "none") ? "ok" : "WRONG";
  return "unknown";
}
