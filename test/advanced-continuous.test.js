// Advanced continuous mathematics: probe corpus (multivariable and vector calculus, transforms,
// complex analysis, numerical methods, curves, PDE basics).
//
// The expected values in advanced-continuous.corpus.js come from an OFFLINE sympy/mpmath oracle
// (tools/quelvra-advanced-oracle.py); nothing from it is shipped. Every probe goes through the
// public solve() entry. A probe is
//   correct : the answer matches the oracle AND Quelvra's own verification passed
//             (or: a refusal was expected and Quelvra refused)
//   refused : Quelvra declined to answer
//   wrong   : Quelvra showed an answer that does not match (or an unverified answer, or it
//             answered where a refusal was expected)
// The hard rule is zero wrong answers. QV_ADV_REPORT=1 prints every probe.

import { test, ok } from "./harness.js";
import { CORPUS } from "./advanced-continuous.corpus.js";
import { solve } from "../public/engine/quelvra.js";
import { parse } from "../public/engine/parse.js";
import { toText } from "../public/engine/print.js";
import * as X from "../public/engine/expr.js";
import { evalC, truth } from "../public/engine/verify.js";

const REPORT = !!process.env.QV_ADV_REPORT;
const FILTER = process.env.QV_ADV_AREA || "";
const MIN_CORRECT = { multivariable: 0.9, vector: 0.9, transforms: 0.9, complex: 0.9, numerical: 0.9, curves: 0.9, pde: 0.9 };

const P = (s) => parse(String(s));
const SAMPLE = [0.37, 1.23, 2.1, -0.71, 1.7, 0.93, -1.37];
const bad = (c) => !c || !Number.isFinite(c.re) || !Number.isFinite(c.im);
function stripO(u) {
  if (!u) return u;
  if (u.k === "add") return X.add(...u.args.filter((a) => !(a.k === "fn" && a.name === "O")));
  return u;
}
// the evaluator has no step function: heaviside(u) -> piecewise(1, u > 0, 0)
const noStep = (u) => X.mapTree(u, (w) => (w.k === "fn" && w.name === "heaviside" && w.args.length === 1 ? X.piecewise(X.ONE, X.rel(">", w.args[0], X.ZERO), X.ZERO, X.TRUE) : w));
// numeric equality of two trees at sample points (complex arithmetic, relative tolerance)
function sameFn(a, b, { vars = null, tol = 1e-7, min = 3, points = null } = {}) {
  if (!a || !b) return false;
  a = noStep(stripO(a)); b = noStep(stripO(b));
  const names = [...new Set([...X.freeSymbols(a), ...X.freeSymbols(b)])];
  let good = 0;
  for (let i = 0; i < 7; i++) {
    const env = {};
    names.forEach((nm, j) => { env[nm] = vars && vars[nm] ? vars[nm][i % vars[nm].length] : SAMPLE[(i + 2 * j) % SAMPLE.length] + 0.011 * j; });
    if (points) Object.assign(env, points[i % points.length]);
    const va = evalC(a, env, "complex"), vb = evalC(b, env, "complex");
    if (bad(va) || bad(vb)) continue;
    const sc = Math.max(1, Math.hypot(va.re, va.im), Math.hypot(vb.re, vb.im));
    if (Math.hypot(va.re - vb.re, va.im - vb.im) > tol * sc) return false;
    good++;
  }
  return good >= Math.min(min, 3);
}
const atN = (a, b) => sameFn(a, b, { vars: { n: [1, 2, 3, 4, 5, 6, 7] }, tol: 1e-7 });
const refusedR = (r) => !r.ok || !(r.answers || []).length || r.answers.every((a) => a.kind === "none");
const exactAns = (r, label) => (r.answers || []).find((a) => a.tree && (!label || a.label === label || (a.label || "").toLowerCase().startsWith(label.toLowerCase())));
const byLabel = (r, label) => (r.answers || []).find((a) => (a.label || "").toLowerCase() === label.toLowerCase());
const show = (r) => (r.answers || []).map((a) => `${a.label || a.kind}: ${a.values ? a.values.map(([k, v]) => `${k}=${toText(v)}`).join(",") : a.tree ? toText(a.tree) : a.approx ? a.approx.value : ""}`).join(" | ");
const TYPE_WORD = { min: "minimum", max: "maximum", saddle: "saddle", inconclusive: "inconclusive", candidate: "" };

function vecEntries(u) { return u && (u.k === "vector" || u.k === "tuple") ? u.args : null; }
function judge(want, r) {
  if (want.refuse) return refusedR(r) ? "correct" : "wrong";
  if (refusedR(r)) return "refused";
  const verified = r.verification && r.verification.status === "passed";
  const res = check(want, r);
  if (res && verified) return "correct";
  return "wrong";
}
function check(want, r) {
  if (want.value !== undefined) {
    const a = exactAns(r, want.label);
    return !!a && sameFn(a.tree, P(want.value), { vars: want.vars });
  }
  if (want.laurent !== undefined) {
    const a = exactAns(r, "Laurent") || exactAns(r);
    return !!a && sameFn(a.tree, P(want.laurent), { vars: { z: [0.13, -0.21, 0.17, 0.08, -0.11] } });
  }
  if (want.vector) {
    const a = exactAns(r, want.label);
    const es = a && vecEntries(a.tree);
    return !!es && es.length === want.vector.length && es.every((e, i) => sameFn(e, P(want.vector[i])));
  }
  if (want.matrix) {
    const a = exactAns(r);
    if (!a || a.tree.k !== "matrix") return false;
    const rows = a.tree.args;
    return rows.length === want.matrix.length && rows.every((row, i) => row.args.length === want.matrix[i].length && row.args.every((e, j) => sameFn(e, P(want.matrix[i][j]))));
  }
  if (want.bool !== undefined) {
    const a = (r.answers || []).find((x) => x.tree && x.tree.k === "bool");
    if (!a || a.tree.v !== want.bool) return false;
    if (want.potential) { const p = byLabel(r, "potential"); if (!p || !constDiff(p.tree, P(want.potential))) return false; }
    if (want.where) { const s = (r.answers || []).find((x) => x.kind === "set"); if (!s || !sameRegion(s.tree, P(want.where), ["x", "y"])) return false; }
    return true;
  }
  if (want.potential) { const p = byLabel(r, "potential") || exactAns(r); return !!p && constDiff(p.tree, P(want.potential)); }
  if (want.differential) {
    const a = exactAns(r);
    if (!a) return false;
    const vs = Object.keys(want.differential);
    return vs.every((v) => { const env = {}; vs.forEach((w2) => { env["d" + w2] = w2 === v ? X.ONE : X.ZERO; }); return sameFn(X.subs(a.tree, env), P(want.differential[v])); });
  }
  if (want.plane) {
    const a = exactAns(r);
    if (!a || a.tree.k !== "eq") return false;
    const g = X.sub(a.tree.args[0], a.tree.args[1]), e = P(want.plane);
    const h = X.sub(e.args[0], e.args[1]);
    let ratio = null;
    for (const [xv, yv, zv] of [[0.3, 1.7, -0.4], [2.1, -0.6, 0.9], [-1.2, 0.4, 2.2], [0.7, 0.2, 0.1]]) {
      const env = { x: xv, y: yv, z: zv };
      const gv = evalC(g, env), hv = evalC(h, env);
      if (bad(gv) || bad(hv) || Math.abs(hv.re) < 1e-9) return false;
      const q = gv.re / hv.re;
      if (ratio === null) ratio = q; else if (Math.abs(q - ratio) > 1e-8 * Math.max(1, Math.abs(ratio))) return false;
    }
    return ratio !== null && Math.abs(ratio) > 1e-12;
  }
  if (want.points || want.candidates) {
    const list = want.points || want.candidates;
    const sols = (r.answers || []).filter((a) => a.kind === "solution");
    if (sols.length !== list.length) return false;
    return list.every(([pt, kind]) => sols.some((s) => {
      const m = new Map(s.values.map(([k, v]) => [k, v]));
      if (!Object.entries(pt).every(([k, v]) => m.has(k) && sameFn(m.get(k), P(v)))) return false;
      if (want.candidates) return m.has("f") && sameFn(m.get("f"), P(kind));
      return kind.split("|").some((kw) => (s.label || "").toLowerCase().includes(TYPE_WORD[kw]));
    }));
  }
  if (want.extrema) {
    const mx = byLabel(r, "Maximum value"), mn = byLabel(r, "Minimum value");
    return !!mx && !!mn && sameFn(mx.tree, P(want.extrema.max)) && sameFn(mn.tree, P(want.extrema.min));
  }
  if (want.fourier) {
    const a0 = byLabel(r, "a0"), an = byLabel(r, "an"), bn = byLabel(r, "bn");
    return !!(a0 && an && bn) && sameFn(a0.tree, P(want.fourier.a0)) && atN(an.tree, P(want.fourier.an)) && atN(bn.tree, P(want.fourier.bn));
  }
  if (want.bn || want.an) {
    const lab = want.bn ? "bn" : "an";
    const a = byLabel(r, lab);
    return !!a && atN(a.tree, P(want[lab]));
  }
  if (want.residues) {
    const rs = (r.answers || []).filter((a) => a.tree && a.at);
    if (rs.length !== want.residues.length) return false;
    return want.residues.every(([pt, v]) => rs.some((a) => sameFn(a.at, P(pt)) && sameFn(a.tree, P(v))));
  }
  if (want.approx !== undefined) {
    const a = (r.answers || []).find((x) => x.approx) || (r.answers || []).find((x) => x.tree);
    if (!a) return false;
    const v = a.approx ? parseFloat(a.approx.value) : evalC(a.tree, {}).re;
    return Math.abs(v - want.approx) <= (want.tol || 1e-8) * Math.max(1, Math.abs(want.approx));
  }
  if (want.type) {
    const a = byLabel(r, "Type");
    return !!a && a.tree.k === "sym" && a.tree.name === want.type;
  }
  if (want.regions) {
    return Object.entries(want.regions).every(([kind, rel]) => {
      const a = (r.answers || []).find((x) => x.kind === "set" && (x.label || "").toLowerCase() === kind);
      return !!a && sameRegion(a.tree, P(rel), ["x", "y"]);
    });
  }
  return false;
}
function constDiff(a, b) {
  const d = X.sub(a, b);
  let first = null;
  for (let i = 0; i < 6; i++) {
    const env = { x: SAMPLE[i], y: SAMPLE[(i + 2) % 7], z: SAMPLE[(i + 4) % 7] };
    const v = evalC(d, env);
    if (bad(v)) return false;
    if (first === null) first = v.re; else if (Math.abs(v.re - first) > 1e-8 * Math.max(1, Math.abs(first))) return false;
  }
  return true;
}
function sameRegion(a, b, vars) {
  const grid = [-2, -1, -0.5, 0, 0.5, 1, 2];
  for (const xv of grid) for (const yv of grid) {
    const env = { [vars[0]]: xv, [vars[1]]: yv };
    const ta = truth(a, env), tb = truth(b, env);
    if (ta !== tb) return false;
  }
  return true;
}

// ------------------------------------------------------------------ run the corpus once
const results = [];
function runAll() {
  if (results.length) return results;
  for (const c of CORPUS) {
    if (FILTER && c.area !== FILTER) continue;
    for (const qtext of c.qs) {
      let r;
      const t0 = Date.now();
      try { r = solve(qtext, { timeLimit: 20000 }); } catch (e) { r = { ok: false, answers: [], error: { message: `CRASH ${e && e.message}` } }; }
      const verdict = judge(c.want, r);
      results.push({ area: c.area, q: qtext, verdict, ms: Date.now() - t0, r });
      if (REPORT) console.log(`${verdict.padEnd(8)} [${c.area}] ${qtext}  ->  ${refusedR(r) ? "REFUSED " + ((r.answers && r.answers[0] && r.answers[0].label) || (r.error && r.error.message) || "") : show(r)}  (${r.verification ? r.verification.status : "-"}, ${Date.now() - t0} ms)`);
    }
  }
  return results;
}
export function tally() {
  const by = {};
  for (const x of runAll()) {
    const t = by[x.area] || (by[x.area] = { correct: 0, refused: 0, wrong: 0, total: 0 });
    t[x.verdict]++; t.total++;
  }
  return by;
}

test("advanced continuous corpus: per-area table and zero wrong answers", () => {
  const by = tally();
  const rows = Object.entries(by).map(([a, t]) => `  ${a.padEnd(14)} ${String(t.correct).padStart(4)} correct ${String(t.refused).padStart(4)} refused ${String(t.wrong).padStart(4)} wrong  / ${t.total}`);
  console.log("     advanced-continuous probes:\n" + rows.join("\n"));
  const wrong = results.filter((x) => x.verdict === "wrong");
  ok(!wrong.length, `wrong answers: ${wrong.map((x) => `[${x.area}] ${x.q} -> ${show(x.r)} (${x.r.verification && x.r.verification.status})`).join("\n   ")}`);
});
test("advanced continuous corpus: coverage per area", () => {
  const by = tally();
  for (const [a, t] of Object.entries(by)) {
    const need = MIN_CORRECT[a] || 0;
    ok(t.correct / t.total >= need, `${a}: ${t.correct}/${t.total} correct, need ${Math.round(need * 100)}%; refused: ${results.filter((x) => x.area === a && x.verdict === "refused").map((x) => x.q).join("; ")}`);
  }
});
