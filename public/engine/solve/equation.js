// Quelvra solvers: one equation in one unknown -> orchestrator candidate.
//
// solveCore produces a superset of candidates (every transformation is an equivalence or an
// implication). Here each candidate is checked against the ORIGINAL equation (env.original,
// never the transformed one): exact candidates by exact simplification or by multiprecision
// evaluation at 40 and 80 digits, periodic families through two representatives (their period is
// a period of the equation), approximate roots through their certified enclosure. Extraneous
// candidates are listed in `rejected` with the reason. verify() runs verify.js on every answer
// against env.original and adds the completeness argument (Sturm count, equivalence chain,
// interval-arithmetic proof, or an honest "incomplete").

import * as X from "../expr.js";
import * as Q from "../num.js";
import { toText } from "../print.js";
import { verifySolution, evalC } from "../verify.js";
import { toContractVerification } from "../orchestrate.js";
import { C, safe, fail, unwrap, difference, checkCandidate, dedupeTrees, cval, hp, nearZero, isZeroExact, cmpConst, signConst,
  exactAnswer, verifyRootsWithVerifyJs, decimalTree, passCheck, failCheck, openCheck, makeCompare, hasFn, tidy, isConstTree, denominators, rationalBetween } from "./util.js";
import { solveCore, mergeSol, emptySol } from "./core.js";
import { solveLiteral, coeffTrees, isRationalPoly, toUPoly } from "./poly.js";
import { evalWTree } from "./lambert.js";
import { certifiedRoots, numeratorForNumerics } from "./numeric.js";
import { normalizeSet } from "./inequality.js";
import * as P from "../poly.js";

export function equationTarget(node, card, env) {
  const { node: inner, vars } = unwrap(node);
  const eqn = inner.k === "eq" ? inner : inner.k === "rel" ? null : X.eq(inner, X.ZERO);
  if (!eqn) return null;
  const syms = [...X.freeSymbols(eqn)].filter((s) => s !== "k" || true);
  let x = vars[0] || (env.options && env.options.variable) || (card && card.unknowns && card.unknowns[0]) || null;
  if (!x) x = syms.includes("x") ? "x" : syms.length === 1 ? syms[0] : null;
  if (!x || !syms.includes(x)) return null;
  const params = syms.filter((s) => s !== x);
  return { eqn, x, params };
}

// Main entry. mode: "exact" (all exact methods + numeric fallback) | "numeric-check" (independent
// numeric cross-check).
export function solveEquation(node, card, env, mode = "exact") {
  const tg = equationTarget(node, card, env);
  if (!tg) return null;
  const { eqn, x, params } = tg;
  const dom = env.domain || "real";
  const log = env.log;
  const digits = env.digits || 20;
  const opts = env.options || {};
  const original = eqn;
  if (params.length) return mode === "exact" ? literalCandidate(eqn, x, params, env) : null;
  const e = difference(eqn, dom);
  if (mode === "numeric-check") return numericCandidate(e, x, original, env);
  const iv = parseInterval(opts.interval);
  const S = { x, topVar: x, log, domain: dom, digits, checkTime: env.checkTime, allowNumeric: true, interval: iv, depth: 0 };
  log.add({ rule: "solve.start", title: "Move everything to one side", why: "Solve f(x) = 0 where f is the difference of the two sides.", before: eqn, after: X.eq(e, X.ZERO) });
  const sol = solveCore(e, S);
  return assemble(sol, e, x, original, env, iv);
}

function parseInterval(iv) {
  if (!iv) return null;
  if (Array.isArray(iv) && iv.length === 2) {
    const [a, b] = iv.map((v) => (typeof v === "number" ? v : cval(typeof v === "object" ? v : X.num(Q.fromDecimal ? Q.fromDecimal(String(v)) : Q.Q(BigInt(v)))).re));
    if (Number.isFinite(a) && Number.isFinite(b) && a < b) return [a, b];
  }
  return null;
}

// ---------------------------------------------------------------- assembly
export function assemble(sol, e, x, original, env, iv) {
  const dom = env.domain || "real";
  const digits = env.digits || 20;
  const log = env.log;
  const rejected = [];
  const conditions = [];
  const answers = [];
  const checked = []; // { tree, level, multiplicity, approx?, lambert? }
  // exact candidates
  const cands = dedupeTrees(sol.exact.map((r) => ({ ...r, tree: tidy(r.tree, dom) })), dom);
  for (const c of cands) {
    env.checkTime && env.checkTime();
    if (hasFn(c.tree, "W")) {
      const r = checkW(original, x, c.tree, dom, digits);
      if (r.ok) checked.push({ ...c, level: "numeric", approx: r.approx, lambert: true });
      else rejected.push({ tree: X.eq(X.sym(x), c.tree), value: c.tree, reason: r.reason });
      continue;
    }
    const r = checkCandidate(original, x, c.tree, dom);
    if (r.ok) checked.push({ ...c, level: r.level });
    else rejected.push({ tree: X.eq(X.sym(x), c.tree), value: c.tree, reason: r.reason });
  }
  // approximate candidates
  const approx = [];
  for (const a of sol.approx) {
    if (a.complex) { if (dom === "complex") approx.push(a); continue; }
    const r = checkApprox(original, x, a);
    if (r.ok) approx.push(a);
    else rejected.push({ tree: X.eq(X.sym(x), decimalTree(a.approx.value) || X.sym(x)), value: a.approx.value, reason: r.reason });
  }
  // periodic families
  let fams = [];
  for (const f of sol.general) {
    const reps = [f.offset, C(X.add(f.offset, f.period), dom)];
    let bad = null;
    for (const t of reps) { const r = checkCandidate(original, x, t, dom); if (!r.ok) { bad = r.reason; break; } }
    if (bad) rejected.push({ tree: X.eq(X.sym(x), C(X.add(f.offset, X.mul(f.period, X.sym("k"))), dom)), value: f.offset, reason: `${bad} (at x = ${toText(f.offset)})` });
    else fams.push(f);
  }
  fams = mergeFamilies(fams, dom);
  if (iv && fams.length) {
    // principal solutions in the interval
    for (const f of fams) {
      const o = cval(f.offset).re, p = cval(f.period).re;
      const k0 = Math.ceil((iv[0] - o) / p - 1e-9), k1 = Math.floor((iv[1] - o) / p + 1e-9);
      for (let k = k0; k <= k1 && k - k0 < 1000; k++) {
        const t = tidy(X.add(f.offset, X.mul(X.num(Q.Q(BigInt(k))), f.period)), dom);
        const v = cval(t).re;
        if (v < iv[0] - 1e-9 || v > iv[1] + 1e-9) continue;
        const inLo = v > iv[0] + 1e-9 || cmpConst(t, decimalTree(String(iv[0])) || X.num(0), dom) >= 0;
        const inHi = v < iv[1] - 1e-9 || cmpConst(t, decimalTree(String(iv[1])) || X.num(0), dom) <= 0;
        if (inLo && inHi) checked.push({ tree: t, multiplicity: 1, level: "exact", fromFamily: true });
      }
    }
    fams = [];
  }
  if (iv) {
    // distinct real roots before restricting to the interval (for the Sturm completeness check)
    sol.preIntervalCount = dedupeTrees(checked, dom).length;
    const edge = (v) => (Number.isFinite(v) ? decimalTree(String(v)) || X.num(Q.Q(BigInt(Math.round(v)))) : null);
    for (let i = checked.length - 1; i >= 0; i--) {
      const t = checked[i].tree, v = checked[i].lambert ? parseFloat(checked[i].approx.value) : cval(t).re;
      let inside;
      if (v > iv[0] + 1e-9 && v < iv[1] - 1e-9) inside = true;
      else if (v < iv[0] - 1e-9 || v > iv[1] + 1e-9) inside = false;
      else inside = (!Number.isFinite(iv[0]) || checked[i].lambert || cmpConst(t, edge(iv[0]), dom) >= 0) && (!Number.isFinite(iv[1]) || checked[i].lambert || cmpConst(t, edge(iv[1]), dom) <= 0);
      if (!inside) checked.splice(i, 1);
    }
  }
  const dedup = dedupeTrees(checked, dom);
  dedup.sort((a, b) => numOf(a) - numOf(b));
  // answers
  for (const c of dedup) {
    if (c.lambert) answers.push({ kind: "approx", label: x, approx: c.approx, closedForm: c.tree, note: `${x} = ${toText(c.tree)} (Lambert W)` });
    else answers.push(exactAnswer(x, c.tree, digits, c.multiplicity > 1 ? { multiplicity: c.multiplicity } : {}));
  }
  for (const a of approx.sort((p, q) => p.value - q.value)) answers.push({ kind: "approx", label: x, approx: a.approx, ...(a.multiplicity > 1 ? { multiplicity: a.multiplicity } : {}) });
  for (const f of fams) answers.push({ kind: "general", label: x, tree: C(X.add(f.offset, X.mul(f.period, X.sym("k"))), dom), param: "k", offset: f.offset, period: f.period });
  // regions from identities (absolute value cases, identities)
  let setAnswer = null;
  if (sol.all || sol.regions.length) setAnswer = regionAnswer(sol, x, original, dom, dedup);
  if (setAnswer) {
    answers.length = 0;
    answers.push(setAnswer);
  }
  const complete = sol.complete;
  let noSolution = false;
  if (!answers.length) {
    if (complete) {
      noSolution = true;
      const why = rejected.length ? `every candidate was rejected: ${rejected.map((r) => `${toText(r.value && r.value.k ? r.value : X.sym(String(r.value)))} (${r.reason})`).join("; ")}` : sol.notes.join("; ") || "no candidate solutions";
      answers.push({ kind: "none", label: dom === "real" ? "No real solution" : "No solution", proof: why });
      log.add({ rule: "solve.none", title: "No solution", why: why.charAt(0).toUpperCase() + why.slice(1) + ".", before: original, after: X.FALSE });
    } else {
      answers.push({ kind: "none", label: `No root found${sol.window ? ` in [${sol.window[0]}, ${sol.window[1]}]` : ""}; the search is not proven complete` });
    }
  }
  if (rejected.length) log.add({ rule: "solve.check.reject", title: "Check candidates in the original equation", why: rejected.map((r) => `${toText(r.tree)} is rejected: ${r.reason}`).join(". ") + ".", before: null, after: null, kind: "note" });
  for (const d of denominators(original)) conditions.push(X.rel("!=", d, X.ZERO));
  const anyApprox = answers.some((a) => a.kind === "approx");
  const solutionStatus = !complete ? "partial" : anyApprox ? "approximate" : "exact";
  const reals = answers.flatMap((a) => (a.kind === "exact" ? [cval(a.tree)] : a.kind === "approx" ? [{ re: parseFloat(a.approx.value), im: 0 }] : [])).filter((c) => Math.abs(c.im) < 1e-12).map((c) => c.re);
  const signature = fams.length ? { kind: "general", general: fams.map((f) => ({ offset: cval(f.offset).re, period: cval(f.period).re })) }
    : setAnswer ? { kind: "other" } : { kind: "roots", reals, complete, window: sol.window || (iv ? iv : null) };
  const statement = sol.statement || null;
  const cand = {
    answers, solutionStatus, rejected, conditions, noSolution,
    note: sol.methods.join(", "),
    extra: { methods: sol.methods, notes: sol.notes, completeness: statement, sturm: sol.sturm },
    signature,
    verify: (c) => verifyEquation(c, original, x, dom, sol, e, iv),
  };
  cand.compare = makeCompare(signature);
  return cand;
}
function numOf(c) { const v = c.approx ? parseFloat(c.approx.value) : cval(c.tree).re; return Number.isFinite(v) ? v : 0; }

function checkW(original, x, tree, dom, digits) {
  const ev = evalWTree(tree, digits + 10);
  if (!ev) return { ok: false, reason: "could not evaluate the Lambert W value" };
  const t = decimalTree(ev.value);
  if (!t) return { ok: false, reason: "could not evaluate the Lambert W value" };
  const r = checkApprox(original, x, { approx: { value: ev.value }, certified: true });
  if (!r.ok) return r;
  const shown = hp(tree.k ? t : t, digits);
  return { ok: true, approx: { value: shown.ok ? shown.rec.value : ev.value, digits, requested: digits, errorBound: `1e-${digits}`, method: "Lambert W (multiprecision Halley, certified by a sign change)", iterations: 0, converged: true } };
}
// An approximate root: certified enclosure (from the solver) + the original is defined there and
// its residual is tiny relative to the size of the sides.
function checkApprox(original, x, a) {
  const t = decimalTree(a.approx.value);
  if (!t) return { ok: false, reason: "unreadable value" };
  if (a.certified === false) return { ok: false, reason: "the root could not be certified" };
  for (const d of denominators(original)) {
    const h = hp(X.subs(d, { [x]: t }), 30);
    if (h.ok && Math.hypot(h.re, h.im) < 1e-12) return { ok: false, reason: `it makes the denominator ${toText(d)} of the original equation (numerically) zero` };
  }
  const L = hp(X.subs(original.args[0], { [x]: t }), 30), R = hp(X.subs(original.args[1], { [x]: t }), 30);
  if (!L.ok || !R.ok) return { ok: false, reason: "the original equation is undefined there" };
  if (Math.abs(L.im) > 1e-15 * Math.max(1, Math.abs(L.re)) || Math.abs(R.im) > 1e-15 * Math.max(1, Math.abs(R.re))) return { ok: false, reason: "a side of the original equation is not real there" };
  const scale = Math.max(1, Math.abs(L.re), Math.abs(R.re));
  if (Math.abs(L.re - R.re) > 1e-12 * scale) return { ok: false, reason: `substituting gives a residual of ${Math.abs(L.re - R.re).toExponential(2)}` };
  return { ok: true };
}

// merge families of equal period whose offsets are equally spaced by period / n
function mergeFamilies(fams, dom) {
  let changed = true;
  fams = fams.slice();
  const val = (t) => cval(t).re;
  // normalise offsets into [0, period) when numeric and cheap
  fams = fams.map((f) => {
    const p = val(f.period), o = val(f.offset);
    if (!(p > 0) || !Number.isFinite(o)) return f;
    const k = Math.floor(o / p + 1e-12);
    if (k === 0 || f.equivalence) return f;
    // prefer offsets in (-period/2, period/2]
    const k2 = Math.round(o / p);
    return k2 === 0 ? f : { ...f, offset: tidy(X.sub(f.offset, X.mul(X.num(Q.Q(BigInt(k2))), f.period)), dom) };
  });
  // duplicates
  const out0 = [];
  for (const f of fams) {
    if (out0.some((g) => samePeriod(g, f, dom) && congruent(g.offset, f.offset, g.period, dom))) continue;
    out0.push(f);
  }
  fams = out0;
  while (changed) {
    changed = false;
    const groups = new Map();
    for (const f of fams) {
      const key = val(f.period).toPrecision(12);
      if (!groups.has(key)) groups.set(key, []);
      groups.get(key).push(f);
    }
    for (const [, g] of groups) {
      if (g.length < 2) continue;
      const P0 = g[0].period, p = val(P0);
      // try every subset size n dividing into an arithmetic progression with step p/n
      for (let n = g.length; n >= 2; n--) {
        const step = C(X.div(P0, X.num(Q.Q(BigInt(n)))), dom);
        for (const base of g) {
          const members = [base];
          for (let j = 1; j < n; j++) {
            const target = C(X.add(base.offset, X.mul(X.num(Q.Q(BigInt(j))), step)), dom);
            const m = g.find((f) => !members.includes(f) && congruent(f.offset, target, P0, dom));
            if (!m) break;
            members.push(m);
          }
          if (members.length === n) {
            fams = fams.filter((f) => !members.includes(f));
            const off = members.reduce((best, f) => (Math.abs(val(f.offset)) < Math.abs(val(best.offset)) - 1e-12 ? f : best), members[0]);
            let o = off.offset;
            const k2 = Math.round(val(o) / val(step) - 0.5 + 1e-12);
            if (k2 !== 0 && Math.abs(val(o)) >= val(step)) o = tidy(X.sub(o, X.mul(X.num(Q.Q(BigInt(k2))), step)), dom);
            fams.push({ offset: o, period: step });
            changed = true;
            break;
          }
        }
        if (changed) break;
      }
      if (changed) break;
    }
  }
  return fams.sort((a, b) => val(a.offset) - val(b.offset));
}
function samePeriod(f, g, dom) { return Math.abs(cval(f.period).re - cval(g.period).re) < 1e-12 * Math.max(1, Math.abs(cval(f.period).re)) && isZeroExact(X.sub(f.period, g.period), dom); }
function congruent(a, b, per, dom) {
  const d = cval(X.div(X.sub(a, b), per)).re;
  if (!Number.isFinite(d) || Math.abs(d - Math.round(d)) > 1e-9) return false;
  const diff = X.sub(X.sub(a, b), X.mul(X.num(Q.Q(BigInt(Math.round(d)))), per));
  return isZeroExact(diff, dom) || nearZero(diff, 50);
}

// identity / abs regions -> set answer (only when the regions are simple)
function regionAnswer(sol, x, original, dom, points) {
  const X0 = X.sym(x);
  const parts = [];
  if (sol.all) parts.push(X.TRUE);
  parts.push(...sol.regions);
  for (const p of points) parts.push(X.eq(X0, p.tree));
  let tree = parts.length === 1 ? parts[0] : X.or(...parts);
  // exclude points where the original is undefined (denominators)
  const excl = [];
  for (const d of denominators(original)) {
    const r = safe(() => solveCore(C(d, dom), { x, topVar: x, log: { add() {}, group: (h, f) => f() }, domain: dom, allowNumeric: false, depth: 0 }));
    if (!r) return null;
    for (const z of r.exact) if (Math.abs(cval(z.tree).im) < 1e-12) excl.push(z.tree);
  }
  if (tree === X.TRUE) {
    return { kind: "all", label: excl.length ? `every real ${x} except ${excl.map((z) => toText(z)).join(", ")} (where the equation is undefined)` : `every real ${x} is a solution`, tree: X.TRUE, excluded: excl };
  }
  if (excl.length) tree = X.and(tree, ...excl.map((z) => X.rel("!=", X0, z)));
  tree = safe(() => C(tree, dom), tree);
  const norm = safe(() => normalizeSet(tree, x));
  if (norm && norm.tree === X.TRUE) return { kind: "all", label: `every real ${x} is a solution`, tree: X.TRUE, excluded: [] };
  if (norm) return { ...norm, excluded: excl };
  const label = tree === X.TRUE ? `every real ${x} is a solution` : `${toText(tree)}`;
  return tree === X.TRUE ? { kind: "all", label, tree: X.TRUE } : { kind: "set", label: x, tree, excluded: excl };
}

// ---------------------------------------------------------------- verification
function verifyEquation(c, original, x, dom, sol, e, iv) {
  const results = [];
  const ans = c.answers;
  if (c.noSolution) {
    results.push(sol.complete ? passCheck("no-solution", `${c.answers[0].proof}; the solving steps are equivalences or implications, so no solution was lost`) : openCheck("no-solution", "search not complete"));
    return toContractVerification(results);
  }
  const roots = ans.filter((a) => a.kind === "exact" || a.kind === "approx");
  const rootResults = verifyRootsWithVerifyJs(original, x, roots.map((a) => (a.closedForm ? { ...a, kind: "approx" } : a)), dom);
  results.push(...rootResults);
  for (const a of ans.filter((q) => q.kind === "general")) {
    for (const k of [-1, 0, 1, 2]) {
      const t = C(X.subs(a.tree, { [a.param]: X.num(Q.Q(BigInt(k))) }), dom);
      const r = verifySolution(original, new Map([[x, t]]), { domain: dom });
      results.push(r.status === "verified-exact" || r.status === "verified-numeric" ? { ...r, checks: r.checks.map((q) => ({ ...q, detail: `k = ${k}: ${q.detail}` })) } : r);
    }
  }
  for (const a of ans.filter((q) => q.kind === "set" || q.kind === "all")) results.push(verifyRegion(a, original, x, dom));
  // completeness
  const real = roots.map((a) => (a.tree && !a.closedForm ? cval(a.tree) : { re: parseFloat(a.approx.value), im: 0 })).filter((z) => Math.abs(z.im) < 1e-12).map((z) => z.re);
  const topPoly = safe(() => { const cs = coeffTrees(e, x); return cs && isRationalPoly(cs); });
  if (topPoly && sol.sturm !== undefined && sol.sturm !== Infinity && dom === "real") {
    const distinct = sol.preIntervalCount !== undefined ? sol.preIntervalCount : real.filter((v, i) => real.findIndex((w) => Math.abs(w - v) <= 1e-12 * Math.max(1, Math.abs(v))) === i).length;
    results.push(distinct === sol.sturm ? passCheck("completeness", `Sturm's theorem: the polynomial has exactly ${sol.sturm} distinct real root${sol.sturm === 1 ? "" : "s"}, and ${distinct} ${distinct === 1 ? "was" : "were"} found${sol.preIntervalCount !== undefined ? " before restricting to the interval" : ""}`) : failCheck("completeness", `Sturm count ${sol.sturm} but ${distinct} listed`));
  } else if (sol.complete) {
    results.push(passCheck("completeness", sol.statement || `every transformation (${sol.methods.join(", ")}) was an equivalence or an implication, and every candidate was checked in the original equation`));
  } else results.push(openCheck("completeness", sol.statement || "the search is not proven complete"));
  // independent numeric sweep: no listed-root-free sign change of the numerator in [-50, 50]
  if (dom === "real" && roots.length + ans.filter((q) => q.kind === "none").length === ans.length) {
    const rej = (c.rejected || []).map((r) => (r.value && r.value.k ? cval(r.value).re : parseFloat(r.value))).filter(Number.isFinite);
    const r = sweepCheck(e, x, real, rej, sweepWindow(iv));
    if (r) results.push(r);
  }
  return toContractVerification(results);
}
function verifyRegion(a, original, x, dom) {
  // probe the set against the original relation
  let bad = null, n = 0;
  for (let i = 0; i <= 200; i++) {
    const t = -10 + i * 0.1 + 0.0123;
    const tq = X.num(Q.Q(BigInt(Math.round(t * 1e4)), 10000n));
    const inSet = a.tree === X.TRUE ? true : safe(() => { const v = C(X.subs(a.tree, { [x]: tq }), dom); return v === X.TRUE ? true : v === X.FALSE ? false : null; });
    if (inSet === null) continue;
    const r = checkCandidate(original, x, tq, dom);
    n++;
    if (r.ok !== inSet) { bad = `disagrees at ${x} = ${toText(tq)}`; break; }
  }
  return bad ? failCheck("set-probe", bad) : passCheck("set-probe", `the solution set matches the original equation at ${n} test points`);
}
// Independent sweep: sign changes of f = LHS - RHS on [-50, 50]; each one is located by bisection and
// must be a listed root, a rejected candidate or a pole / domain edge (|f| does not tend to 0).
function sweepWindow(iv) {
  if (!iv) return [-50, 50];
  const lo = Math.max(-50, iv[0]), hi = Math.min(50, iv[1]);
  return lo < hi ? [lo, hi] : [-50, 50];
}
function sweepCheck(e, x, reals, rejected, win = [-50, 50]) {
  const f = (t) => { const v = evalC(e, { [x]: t }, "complex"); return Math.abs(v.im) < 1e-9 * Math.max(1, Math.abs(v.re)) ? v.re : NaN; };
  const near = (list, a, b) => list.some((r) => r >= a - 1e-7 * Math.max(1, Math.abs(r)) && r <= b + 1e-7 * Math.max(1, Math.abs(r)));
  let prev = null, pt = null;
  const N = 800, h = (win[1] - win[0]) / N;
  for (let i = 0; i <= N; i++) {
    const t = Math.min(win[1], win[0] + i * h + 0.000137 * h * 8);
    const v = f(t);
    if (Number.isFinite(v) && prev !== null && Number.isFinite(prev) && v * prev < 0 && !near(reals, pt, t) && !near(rejected, pt, t)) {
      let a = pt, b = t, fa = prev;
      for (let k = 0; k < 80; k++) { const m = (a + b) / 2, fm = f(m); if (!Number.isFinite(fm)) break; if (fm * fa <= 0) b = m; else { a = m; fa = fm; } }
      const m = (a + b) / 2, fm = Math.abs(f(m));
      if (Number.isFinite(fm) && fm < 1e-6 && !near(reals, a, b) && !near(rejected, a, b)) return failCheck("numeric-sweep", `the equation has a sign change near ${x} = ${m.toPrecision(10)} that no listed root explains`);
    }
    prev = v; pt = t;
  }
  return passCheck("numeric-sweep", `every sign change of the equation on [${win[0]}, ${win[1]}] is explained by a listed root, a rejected candidate or a pole`, "numeric");
}

// ---------------------------------------------------------------- literal (parametric) equations
function literalCandidate(eqn, x, params, env) {
  const dom = env.domain || "real";
  const e = difference(eqn, dom);
  const r = solveLiteral(e, x, { log: env.log, domain: dom, digits: env.digits, checkTime: env.checkTime });
  if (!r) throw fail(`equations in ${x} with parameters ${params.join(", ")} are solved only when linear or quadratic in ${x}`);
  const answers = [...r.answers, ...r.cases];
  const cand = {
    answers, solutionStatus: "exact", rejected: [], conditions: r.conditions,
    note: "parametric", extra: { cases: r.cases, params },
    signature: { kind: "other" },
    verify: () => {
      const res = [];
      for (const a of r.answers) {
        if (a.kind !== "exact") continue;
        const d = C(X.subs(X.sub(eqn.args[0], eqn.args[1]), { [x]: a.tree }), dom);
        const ok = isZeroExact(d, dom);
        // numeric spot checks with random parameter values (condition respected)
        let numOk = 0, numBad = 0;
        for (let s = 0; s < 6; s++) {
          const env0 = new Map();
          params.forEach((p, i) => env0.set(p, X.num(Q.Q(BigInt(((s * 7 + i * 13) % 11) + 2), BigInt((s % 3) + 1)))));
          if (a.condition && safe(() => C(X.subs(a.condition, Object.fromEntries(env0)), dom)) !== X.TRUE) continue;
          const t = C(X.subs(a.tree, Object.fromEntries(env0)), dom);
          const orig = X.subs(eqn, Object.fromEntries(env0));
          const v = verifySolution(orig, new Map([[x, t]]), { domain: dom });
          if (v.status.startsWith("verified")) numOk++; else if (v.status === "failed") numBad++;
        }
        if (!ok && numBad) res.push(failCheck("substitution", `${toText(a.tree)} does not satisfy the equation`));
        else if (ok) res.push(passCheck("substitution-exact", `substituting ${x} = ${toText(a.tree)} simplifies the equation to 0 = 0 (symbolically)${numOk ? `; also checked at ${numOk} random parameter values` : ""}`));
        else res.push(numOk ? passCheck("substitution-numeric", `checked at ${numOk} random parameter values`, "numeric") : openCheck("substitution", "could not check"));
      }
      for (const cs of r.cases) {
        if (!cs.all && !cs.none) continue;
        res.push(passCheck("case", cs.label));
      }
      if (!res.length) res.push(passCheck("no-solution", answers.map((a) => a.label).join("; ")));
      return toContractVerification(res);
    },
  };
  cand.compare = () => true;
  return cand;
}

// ---------------------------------------------------------------- independent numeric cross-check
function numericCandidate(e, x, original, env) {
  const dom = env.domain || "real";
  if (dom !== "real") return null;
  const h = safe(() => C(numeratorForNumerics(e, dom), dom));
  if (!h || X.freeOf(h, x)) return null;
  const W = sweepWindow(parseInterval(env.options && env.options.interval));
  const cr = certifiedRoots(h, x, { lo: W[0], hi: W[1], fixed: true, digits: 20, samples: 1200, timeLimitMs: 2500 });
  const answers = [];
  const rejected = [];
  for (const r of cr.roots) {
    const ok = checkApprox(original, x, { approx: r.approx, certified: r.certified });
    if (ok.ok) answers.push({ kind: "approx", label: x, approx: r.approx });
    else rejected.push({ value: r.approx.value, reason: ok.reason });
  }
  env.log.add({ rule: "solve.numeric.cross-check", title: "Independent numeric root search", why: `Sign changes of ${toText(h)} on [${W[0]}, ${W[1]}], refined in multiprecision.`, before: original, after: null, kind: "approximation" });
  if (!answers.length) answers.push({ kind: "none", label: `No root found in [${W[0]}, ${W[1]}]` });
  const reals = answers.filter((a) => a.approx).map((a) => parseFloat(a.approx.value));
  const signature = { kind: "roots", reals, complete: cr.completeWindow, window: W };
  const cand = {
    answers, solutionStatus: "partial", rejected, conditions: [], signature, note: "numeric cross-check",
    verify: (c) => toContractVerification(verifyRootsWithVerifyJs(original, x, c.answers.filter((a) => a.kind === "approx"), dom).concat([openCheck("completeness", `numeric search on [${W[0]}, ${W[1]}] only`)])),
  };
  cand.compare = makeCompare(signature);
  return cand;
}
