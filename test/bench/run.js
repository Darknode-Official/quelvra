// Quelvra benchmark runner.  node test/quelvra/bench/run.js [category] [--verbose]
// Scores ONLY verified-correct answers: an answer counts when it is mathematically correct
// (compared by equivalence / probing, never by text) AND Quelvra's own verification passed.

import { CORPUS } from "./corpus.js";
import { solve } from "../../public/engine/quelvra.js";
import { parse } from "../../public/engine/parse.js";
import { simplify } from "../../public/engine/simplify.js";
import { toText } from "../../public/engine/print.js";
import * as X from "../../public/engine/expr.js";
import { equivalent, evalC, evalReal, truth } from "../../public/engine/verify.js";

const args = process.argv.slice(2);
const verbose = args.includes("--verbose") || args.includes("-v");
const filter = args.find((a) => !a.startsWith("-"));

const P = (s) => simplify(parse(s));
const num = (a) => {
  if (a.tree) { const c = evalC(a.tree, {}, "complex"); return c; }
  if (a.approx) return { re: parseFloat(a.approx.value), im: 0 };
  return null;
};
const close = (c, d, tol = 1e-7) => c && d && Math.hypot(c.re - d.re, c.im - d.im) <= tol * Math.max(1, Math.hypot(d.re, d.im));

function judge(exp, r, opts) {
  const answers = (r.answers || []);
  const verified = r.verification && r.verification.status === "passed";
  if (exp.refuse) return r.ok === false || answers.every((a) => a.kind === "none") ? "pass" : `answered ${answers.map(show).join("; ")}`;
  if (!r.ok) return `not ok: ${r.error ? r.error.message : answers.map((a) => a.label).join("; ")}`;
  if (exp.none) {
    if (r.noSolution || (answers.length === 1 && answers[0].kind === "none" && r.solutionStatus === "exact") || (answers[0] && answers[0].kind === "set" && answers[0].tree === X.FALSE)) return "pass";
    return `expected no solution, got ${answers.map(show).join("; ")}`;
  }
  if (exp.diverges) {
    const a = answers[0];
    return a && a.kind === "none" && /diverg/i.test(a.label || "") ? "pass" : `expected divergence, got ${answers.map(show).join("; ")}`;
  }
  if (!verified) return `not verified (${r.verification && r.verification.status}): ${answers.map(show).join("; ")}`;
  if (exp.value !== undefined) {
    const a = answers.find((x) => x.tree);
    if (!a) return "no exact answer";
    if (exp.value === "undefined") return a.tree === X.UNDEF ? "pass" : `got ${show(a)}`;
    if (exp.value === "true" || exp.value === "false") return toText(a.tree) === exp.value ? "pass" : `got ${show(a)}`;
    if (exp.value === "oo") return a.tree === X.OO ? "pass" : `got ${show(a)}`;
    const want = P(exp.value);
    if (a.tree.k === "matrix" || want.k === "matrix") return a.tree === want ? "pass" : `got ${show(a)}`;
    const e = equivalent(a.tree, want);
    return e.status.startsWith("equivalent") ? "pass" : `got ${show(a)} expected ${exp.value}`;
  }
  if (exp.approx !== undefined) {
    const a = answers.find((x) => x.approx) || answers.find((x) => x.tree);
    const v = a && num(a);
    return v && Math.abs(v.re - exp.approx) <= (exp.tol || 1e-8) ? "pass" : `got ${a ? show(a) : "nothing"}`;
  }
  if (exp.anti) {
    const a = answers.find((x) => x.tree);
    if (!a) return "no antiderivative";
    const d = X.freeSymbols(a.tree).size ? null : null;
    // compare up to a constant: F - G must be constant; probe at several points
    const x = exp.var || "x";
    const F = a.tree, G = P(exp.anti);
    const pts = [0.3, 0.7, 1.3, 2.1, 0.55, 1.7].map((t) => evalReal(F, { [x]: t }) - evalReal(G, { [x]: t })).filter(Number.isFinite);
    if (pts.length < 3) return `could not compare ${show(a)}`;
    return pts.every((v) => Math.abs(v - pts[0]) < 1e-8 * Math.max(1, Math.abs(pts[0]))) ? "pass" : `got ${show(a)}`;
  }
  if (exp.roots) {
    const sols = answers.filter((a) => a.kind === "exact" || a.kind === "approx");
    // symbolic roots (parameters): compare by equivalence, not by numeric value
    if (exp.roots.some((s) => X.freeSymbols(P(s)).size)) {
      if (sols.length !== exp.roots.length) return `expected ${exp.roots.length} solutions, got ${sols.map(show).join("; ") || "none"}`;
      for (const w of exp.roots) if (!sols.some((g) => g.tree && equivalent(g.tree, P(w)).status.startsWith("equivalent"))) return `missing ${w}; got ${sols.map(show).join("; ")}`;
      return "pass";
    }
    const want = exp.roots.map((s) => evalC(P(s), {}, "complex"));
    const got = sols.map(num);
    if (got.length !== want.length) return `expected ${exp.roots.length} solutions, got ${sols.map(show).join("; ") || "none"}`;
    for (const w of want) if (!got.some((g) => close(g, w))) return `missing ${exp.roots.join(", ")}; got ${sols.map(show).join("; ")}`;
    return "pass";
  }
  if (exp.general) {
    const g = answers.filter((a) => a.kind === "general" || a.kind === "exact");
    if (!g.length) return "no general solution";
    for (const c of exp.contains) {
      const target = evalReal(P(c), {});
      const hit = g.some((a) => {
        if (a.kind === "exact") return close(num(a), { re: target, im: 0 });
        for (let k = -3; k <= 3; k++) if (Math.abs(evalReal(a.tree, { [a.param || "k"]: k }) - target) < 1e-9) return true;
        return false;
      });
      if (!hit) return `general solution does not contain ${c}: ${g.map(show).join("; ")}`;
    }
    return "pass";
  }
  if (exp.set) {
    const a = answers.find((x) => x.kind === "set");
    if (!a) return `no set answer: ${answers.map(show).join("; ")}`;
    const want = parse(exp.set);
    const x = exp.var || "x";
    for (let i = 0; i <= 400; i++) {
      for (const t of [-10 + i * 0.05, -10 + i * 0.05 + 1e-7]) {
        const tw = truth(want, { [x]: t }), tg = truth(a.tree, { [x]: t });
        if (tw === null) continue;
        if (tw !== tg) return `set differs at ${x} = ${t.toFixed(4)}: got ${show(a)}`;
      }
    }
    return "pass";
  }
  if (exp.system) {
    const a = answers.find((x) => x.kind === "solution");
    if (!a || answers.filter((x) => x.kind === "solution").length !== 1) return `expected one solution: ${answers.map(show).join("; ")}`;
    for (const [k, v] of Object.entries(exp.system)) {
      const got = a.values.find(([n]) => n === k);
      if (!got || !close(evalC(got[1], {}, "complex"), evalC(P(v), {}, "complex"))) return `wrong ${k}: ${show(a)}`;
    }
    return "pass";
  }
  if (exp.solutions) {
    const sols = answers.filter((x) => x.kind === "solution");
    if (sols.length !== exp.solutions.length) return `expected ${exp.solutions.length} solutions: ${answers.map(show).join("; ")}`;
    for (const w of exp.solutions) {
      const hit = sols.some((s) => Object.entries(w).every(([k, v]) => { const g = s.values.find(([n]) => n === k); return g && close(evalC(g[1], {}, "complex"), evalC(P(v), {}, "complex")); }));
      if (!hit) return `missing ${JSON.stringify(w)}`;
    }
    return "pass";
  }
  return "unknown expectation";
}
function show(a) {
  if (!a) return "";
  if (a.values) return a.values.map(([k, v]) => `${k} = ${toText(v)}`).join(", ");
  if (a.tree) return (a.label ? a.label + " = " : "") + toText(a.tree);
  if (a.approx) return (a.label ? a.label + " ~ " : "~") + a.approx.value;
  return a.label || a.kind;
}

const byCat = new Map();
let pass = 0, total = 0;
const t0 = Date.now();
const fails = [];
for (const [cat, input, exp, opts] of CORPUS) {
  if (filter && cat !== filter) continue;
  total++;
  let verdict;
  const ts = Date.now();
  try { verdict = judge(exp, solve(input, { ...(opts || {}), timeLimit: 6000 }), opts); } catch (e) { verdict = `CRASH ${e.message}`; }
  const ms = Date.now() - ts;
  const c = byCat.get(cat) || { pass: 0, total: 0 };
  c.total++;
  if (verdict === "pass") { c.pass++; pass++; } else fails.push([cat, input, verdict, ms]);
  byCat.set(cat, c);
  if (verbose) console.log(`${verdict === "pass" ? "ok  " : "FAIL"} [${cat}] ${input}${verdict === "pass" ? "" : "  -> " + verdict}  (${ms} ms)`);
}
if (!verbose) for (const [cat, input, v, ms] of fails) console.log(`FAIL [${cat}] ${input}  -> ${v}  (${ms} ms)`);
console.log("");
for (const [cat, c] of byCat) console.log(`${cat.padEnd(10)} ${String(c.pass).padStart(3)}/${String(c.total).padEnd(3)} ${((100 * c.pass) / c.total).toFixed(0)}%`);
console.log(`\nverified-correct: ${pass}/${total} (${((100 * pass) / total).toFixed(1)}%) in ${((Date.now() - t0) / 1000).toFixed(2)} s`);
