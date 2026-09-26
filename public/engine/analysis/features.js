// Quelvra function analysis commands: domain, range, zeros, intercepts, asymptotes, extrema,
// critical, inflection, monotonic, tangent, normal.
//
// Each command returns an orchestrator candidate whose verify() evaluates the ORIGINAL function
// with the verifier's own double evaluator (verify.js), never with the engines used to derive it.

import { toContractVerification } from "../orchestrate.js";
import { diff } from "../calc/diff.js";
import { expand } from "../simplify.js";
import { limit } from "../calc/limit.js";
import { solveEquation } from "../solve/equation.js";
import * as P from "../poly.js";
import { X, Q, toText, C, safe, fail, dv, valueAt, fAt, definedNum, setTree, ivOut, ivsText, inIvs, probeGrid, pass, bad, open, fmt, ptText, fnAndVar, constArg, tidy, familyMembers, periodOf, hp, approxRec, isZeroExact } from "./util.js";
import { domainSet, verifyDomain, components } from "./domainset.js";
import { analyze, images, monotonePieces, secondChart, inflections, endValue, isNegInf, NEG_OO } from "./core.js";

const TCV = (list) => toContractVerification(list);
const note = (env, rule, title, why, extra = {}) => env.log.add({ rule, title, why, kind: "note", ...extra });
const Y = (x) => (x === "y" ? "f" : "y");
const scale = (v) => Math.max(1, Math.abs(v));

// ---------------------------------------------------------------- numeric evidence helpers
// f along a sequence approaching `at` (tree or +-oo) from `dir`; checks convergence to L (tree / +-oo).
export function sequenceCheck(f, x, at, dir, L) {
  const pts = [];
  const a = at === X.OO ? Infinity : isNegInf(at) ? -Infinity : dv(at);
  // towards +-oo: powers of 2 up to ~5e3 (exp-type f overflows doubles near 710) then powers of 10 up to 1e12
  const far = [...Array.from({ length: 12 }, (_, k) => 1.37 * 2 ** (k + 1)), ...Array.from({ length: 9 }, (_, k) => 1.37 * 10 ** (k + 4))];
  if (a === Infinity) pts.push(...far);
  else if (a === -Infinity) pts.push(...far.map((t) => -t));
  else for (let k = 2; k <= 11; k++) pts.push(a + (dir === "-" ? -1 : 1) * 1.37 * 10 ** -k * scale(a));
  const inf = L === X.OO ? 1 : isNegInf(L) ? -1 : 0;
  // an overflow to the claimed infinity counts as a value on the way there
  const vals = pts.map((t) => fAt(f, x, t)).filter((v) => Number.isFinite(v) || (inf && v === inf * Infinity));
  if (vals.length < 4) return open("sequence", `too few points near ${fmt(a)} where f can be evaluated`);
  const where = `${x} -> ${Number.isFinite(a) ? fmt(a) + (dir || "") : a > 0 ? "oo" : "-oo"}`;
  if (inf) {
    const mags = vals.map((v) => v * inf);
    const grows = mags.slice(-4).every((m, i, arr) => i === 0 || m >= arr[i - 1] * (1 - 1e-9)) && mags[mags.length - 1] > 0;
    const big = mags[mags.length - 1] >= Math.max(2 * Math.abs(mags[0]), 20);
    return grows && big ? pass("sequence", `f grows to ${inf > 0 ? "+" : "-"}oo along ${where} (last value ${fmt(vals[vals.length - 1])})`)
      : bad("sequence", `f does not tend to ${inf > 0 ? "oo" : "-oo"} as ${where} (values ${vals.slice(-3).map(fmt).join(", ")})`);
  }
  const Lv = dv(L);
  const errs = vals.map((v) => Math.abs(v - Lv));
  const last = errs[errs.length - 1];
  const good = last <= 1e-4 * scale(Lv) || (last <= 0.05 * scale(Lv) && last <= 0.2 * errs[0] + 1e-12);
  return good ? pass("sequence", `f -> ${fmt(Lv)} along ${where} (last error ${last.toExponential(1)})`)
    : bad("sequence", `f does not approach ${fmt(Lv)} as ${where} (last value ${fmt(vals[vals.length - 1])})`);
}
// Richardson central difference of the ORIGINAL f at a (double).
export function numDeriv(f, x, a) {
  const h = 1e-3 * scale(a);
  const D = (hh) => (fAt(f, x, a + hh) - fAt(f, x, a - hh)) / (2 * hh);
  const d1 = D(h), d2 = D(h / 2), d3 = D(h / 4);
  const r1 = (4 * d2 - d1) / 3, r2 = (4 * d3 - d2) / 3;
  return { value: (16 * r2 - r1) / 15, spread: Math.abs(r2 - r1) };
}
const inWin = (res, t) => !res.win || ((res.win.lo === null || t >= dv(res.win.lo) - 1e-12) && (res.win.hi === null || t <= dv(res.win.hi) + 1e-12));
function domainSamples(res, n = 1500) {
  const out = [];
  for (const c of res.comps) {
    const lo = Number.isFinite(c.lo.v) ? c.lo.v : Math.min(-40, (Number.isFinite(c.hi.v) ? c.hi.v : 0) - 40);
    const hi = Number.isFinite(c.hi.v) ? c.hi.v : Math.max(40, (Number.isFinite(c.lo.v) ? c.lo.v : 0) + 40);
    const m = Math.max(50, Math.round(n / res.comps.length));
    for (let i = 0; i <= m; i++) {
      const t = lo + ((hi - lo) * i) / m;
      if ((i === 0 && c.lo.open) || (i === m && c.hi.open)) continue;
      out.push(t);
    }
    for (const cp of res.crit.filter((q) => q.comp === c)) for (const e of [-1e-4, 1e-4]) out.push(cp.v + e * scale(cp.v));
  }
  return out;
}

// ---------------------------------------------------------------- domain
export function cmdDomain(node, env) {
  const { f, x } = fnAndVar(node.args, "domain");
  const d = domainSet(f, x, env);
  note(env, "analysis.domain.conditions", "List the conditions for f to be defined", d.reasons.length ? d.reasons.join("; ") + "." : "No part of the expression restricts the variable (no denominators, even roots, logarithms or inverse trig functions depending on it).");
  env.log.add({ rule: "analysis.domain.solve", title: "Solve the conditions together", why: d.families.length ? "Solve the non-periodic conditions by a sign chart; the periodic conditions exclude whole families of points (k is any integer)." : "Solve the conditions together with a sign chart (exact test point in every interval).", before: f, after: d.tree });
  const answer = { kind: "set", label: "Domain", variable: x, tree: d.tree, interval: ivOut(d.ivs), text: d.text };
  if (d.families.length) { answer.param = "k"; answer.excluded = d.families.map((fm) => ({ offset: fm.offset, period: fm.period })); }
  return { answers: [answer], solutionStatus: d.approx ? "approximate" : "exact", conditions: [], graph: { exprs: [f], marks: [] }, verify: () => TCV([verifyDomain(f, x, d)]) };
}

// ---------------------------------------------------------------- range
export function cmdRange(node, env) {
  const { f, x, rest } = fnAndVar(node.args, "range");
  const res = analyze(f, x, env, { window: windowArg(rest, env) });
  const im = images(res);
  const yv = Y(x);
  const tree = setTree(im.union, yv);
  note(env, "analysis.range.domain", "Domain", `f is defined on ${res.d.text}${res.period ? `; f is periodic with period ${toText(res.period)}, so one full period (a window ${toText(res.win.lo)} <= ${x} <= ${toText(res.win.hi)}) gives every value` : ""}.`);
  env.log.add({ rule: "analysis.range.derivative", title: "Critical points", why: `f'(${x}) = ${toText(res.df)}. ${res.crit.length ? `Critical points: ${res.crit.map((c) => ptText(c)).join(", ")}.` : "There are no critical points."}`, before: res.f, after: res.df });
  const lines = im.parts.map((p) => `on ${compText(p.comp)}: values from ${valText(p.lo)} to ${valText(p.hi)}`);
  note(env, "analysis.range.images", "Values on each piece of the domain", `f is continuous on each piece, so by the intermediate value theorem it takes every value between its smallest and largest value (or limit) there: ${lines.join("; ")}.`);
  env.log.add({ rule: "analysis.range.union", title: "Collect the values", why: "The range is the union of these intervals; an end is included exactly when f attains it.", before: null, after: tree });
  const approx = im.parts.some((p) => p.lo.approx || p.hi.approx);
  return {
    answers: [{ kind: "set", label: "Range", variable: yv, tree, interval: ivOut(im.union), text: ivsText(im.union) }],
    solutionStatus: approx ? "approximate" : "exact", graph: { exprs: [f], marks: [] },
    verify: () => TCV(verifyRange(res, im)),
  };
}
const compText = (c) => `${c.lo.open ? "(" : "["}${c.lo.tree ? toText(c.lo.tree) : "-oo"}, ${c.hi.tree ? toText(c.hi.tree) : "oo"}${c.hi.open ? ")" : "]"}`;
const valText = (r) => (r.inf ? (r.inf > 0 ? "oo" : "-oo") : `${toText(r.tree)}${r.attained ? " (attained)" : " (a limit, not attained)"}`);

function verifyRange(res, im) {
  const out = [];
  const { f0: f, x } = res;
  // (1) every sampled value lies in the claimed range
  let n = 0;
  for (const t of domainSamples(res)) {
    if (!definedNum(f, x, t)) continue;
    const v = fAt(f, x, t);
    if (!inIvs(im.union, v, 1e-9)) return [bad("sample", `f(${fmt(t)}) = ${fmt(v)} is outside the claimed range`)];
    n++;
  }
  if (n < 20) return [open("sample", "too few sample points")];
  out.push(pass("sample", `all ${n} sampled values of the original f lie in the claimed range`));
  // (2) every end of the range is attained (value check) or approached (sequence check)
  for (const iv of im.union) for (const rec of [iv.loRec, iv.hiRec]) {
    if (!rec) continue;
    if (rec.attained) {
      const got = fAt(f, x, dv(rec.at));
      const ok = Number.isFinite(got) && Math.abs(got - rec.v) <= 1e-8 * scale(rec.v);
      out.push(ok ? pass("attained", `f(${toText(rec.at)}) = ${fmt(got)} equals the range end ${toText(rec.tree)}`) : bad("attained", `f(${toText(rec.at)}) = ${fmt(got)}, not ${toText(rec.tree)}`));
    } else out.push(sequenceCheck(f, x, rec.limitAt, rec.dir, rec.tree));
  }
  // (3) infinite ends are approached too
  for (const p of im.parts) for (const rec of [p.lo, p.hi]) if (rec.inf) out.push(sequenceCheck(f, x, rec.limitAt, rec.dir, rec.tree));
  return out;
}

// ---------------------------------------------------------------- zeros / intercepts
function zerosCandidate(f, x, env) {
  const env2 = { ...env, options: { ...(env.options || {}), variable: x, interval: undefined } };
  const c = solveEquation(X.eq(f, X.ZERO), { unknowns: [x], kind: "equation" }, env2, "exact");
  if (!c) throw fail("the equation f = 0 could not be set up");
  return c;
}
export function cmdZeros(node, env) {
  const { f, x } = fnAndVar(node.args, "zeros");
  const c = zerosCandidate(f, x, env);
  const base = c.verify;
  return { ...c, verify: (cc) => {
    const v = base(cc);
    const checks = [...v.checks];
    let failed = v.status === "failed";
    for (const a of c.answers) {
      const t = a.kind === "exact" && a.tree && X.freeSymbols(a.tree).size === 0 ? dv(a.tree) : a.kind === "approx" ? parseFloat(a.approx.value) : NaN;
      if (!Number.isFinite(t)) continue;
      const fv = fAt(f, x, t);
      const ok = Number.isFinite(fv) && Math.abs(fv) <= 1e-7 * Math.max(1, ...[t - 1e-3, t + 1e-3].map((s) => Math.abs(fAt(f, x, s)) || 0));
      if (!ok) failed = true;
      checks.push({ name: "residual", method: "numeric", passed: ok, detail: `f(${fmt(t)}) = ${fmt(fv)}` });
    }
    return { ...v, status: failed ? "failed" : v.status, checks };
  } };
}
export function cmdIntercepts(node, env) {
  const { f, x } = fnAndVar(node.args, "intercepts");
  const answers = [];
  const y0 = valueAt(f, x, X.ZERO);
  if (y0 !== null) answers.push({ kind: "exact", label: "y-intercept", tree: X.tuple(X.ZERO, y0) });
  env.log.add({ rule: "analysis.intercepts.y", title: "y-intercept: set x = 0", why: y0 !== null ? `f(0) = ${toText(y0)}.` : "f is not defined at x = 0, so there is no y-intercept.", before: f, after: y0 || X.UNDEF });
  const c = env.log.group({ rule: "analysis.intercepts.x", title: "x-intercepts: solve f(x) = 0", why: "The graph meets the x-axis where f(x) = 0 (and f is defined)." }, () => zerosCandidate(f, x, env));
  const xs = [];
  for (const a of c.answers) {
    if (a.kind === "exact") { answers.push({ kind: "exact", label: "x-intercept", tree: X.tuple(a.tree, X.ZERO), approx: a.approx }); xs.push(dv(a.tree)); }
    else if (a.kind === "approx") { answers.push({ kind: "approx", label: "x-intercept", approx: a.approx, note: `(${a.approx.value}, 0)` }); xs.push(parseFloat(a.approx.value)); }
    else if (a.kind === "general") answers.push({ kind: "general", label: "x-intercept", tree: X.tuple(a.tree, X.ZERO), param: a.param });
    else if (a.kind === "all") answers.push({ kind: "all", label: "x-intercept", tree: X.TRUE, note: "f is zero everywhere on its domain" });
  }
  if (!answers.length) answers.push({ kind: "none", label: "No intercepts", proof: "f is undefined at x = 0 and f(x) = 0 has no real solution" });
  const complete = c.solutionStatus !== "partial";
  return {
    answers, solutionStatus: complete ? (answers.some((a) => a.kind === "approx") ? "approximate" : "exact") : "partial", conditions: c.conditions || [], rejected: c.rejected || [],
    graph: { exprs: [f], marks: [...(y0 !== null ? [{ x: 0, y: dv(y0), label: "y-intercept", kind: "intercept" }] : []), ...xs.filter(Number.isFinite).map((t) => ({ x: t, y: 0, label: "x-intercept", kind: "intercept" }))] },
    verify: () => {
      const res = [];
      const v0 = fAt(f, x, 0);
      if (y0 !== null) res.push(Math.abs(v0 - dv(y0)) <= 1e-9 * scale(v0) ? pass("y-intercept", `f(0) = ${fmt(v0)}`) : bad("y-intercept", `f(0) = ${fmt(v0)}, not ${toText(y0)}`));
      else res.push(!definedNum(f, x, 0) ? pass("y-intercept", "f is undefined at 0") : bad("y-intercept", `f(0) = ${fmt(v0)} is defined`));
      const ev = c.verify(c);
      res.push({ status: ev.status === "passed" ? (ev.level === "numeric" ? "verified-numeric" : "verified-exact") : ev.status === "failed" ? "failed" : "inconclusive", checks: ev.checks.map((k) => ({ kind: k.name, ok: k.passed, detail: k.detail })) });
      for (const t of xs) {
        if (!Number.isFinite(t)) continue;
        const fv = fAt(f, x, t);
        res.push(Number.isFinite(fv) && Math.abs(fv) < 1e-7 ? pass("x-intercept", `f(${fmt(t)}) = ${fmt(fv)}`) : bad("x-intercept", `f(${fmt(t)}) = ${fmt(fv)} is not 0`));
      }
      return TCV(res);
    },
  };
}

// ---------------------------------------------------------------- asymptotes
const limOf = (f, x, to, dir) => {
  const r = limit(f, X.sym(x), to, dir, { timeLimit: 2500 });
  if (r.status === "exact") return { ok: true, tree: r.value, inf: r.value === X.OO ? 1 : isNegInf(r.value) ? -1 : 0 };
  return { ok: false, dne: r.status === "dne", reason: r.reason };
};
const limText = (l) => (l.ok ? toText(l.tree) : l.dne ? "does not exist" : "unknown");
export function cmdAsymptotes(node, env) {
  const { f: f0, x } = fnAndVar(node.args, "asymptotes");
  const f = C(f0);
  const d = domainSet(f0, x, env);
  const answers = [], rejected = [], checks = [], notes = [];
  let partial = false;
  // vertical: open finite ends of domain intervals
  const ends = [];
  for (const iv of d.ivs) {
    if (iv.lo !== null && iv.loOpen) ends.push({ tree: iv.lo, v: dv(iv.lo), right: true });
    if (iv.hi !== null && iv.hiOpen) ends.push({ tree: iv.hi, v: dv(iv.hi), left: true });
  }
  const pts = [];
  for (const e of ends.sort((a, b) => a.v - b.v)) {
    const p = pts.find((q) => q.tree === e.tree || Math.abs(q.v - e.v) < 1e-12 * scale(e.v));
    if (p) { p.left = p.left || e.left; p.right = p.right || e.right; } else pts.push({ ...e });
  }
  for (const p of pts) {
    const L = p.left ? limOf(f, x, p.tree, "-") : null, R = p.right ? limOf(f, x, p.tree, "+") : null;
    const sides = [L, R].filter(Boolean);
    if (sides.some((s) => !s.ok && !s.dne)) { partial = true; notes.push(`the behaviour near ${x} = ${toText(p.tree)} could not be determined`); continue; }
    const detail = [L ? `f -> ${limText(L)} as ${x} -> ${toText(p.tree)}-` : null, R ? `f -> ${limText(R)} as ${x} -> ${toText(p.tree)}+` : null].filter(Boolean).join("; ");
    if (sides.some((s) => s.ok && s.inf)) {
      answers.push({ kind: "exact", label: "Vertical asymptote", tree: X.eq(X.sym(x), p.tree), detail, limits: { left: L && L.ok ? L.tree : null, right: R && R.ok ? R.tree : null } });
      env.log.add({ rule: "analysis.asymptote.vertical", title: `Vertical asymptote x = ${toText(p.tree)}`, why: `${detail}.`, before: null, after: X.eq(X.sym(x), p.tree) });
      checks.push(() => sides.map((s, i) => (s.ok && s.inf ? sequenceCheck(f0, x, p.tree, (L && i === 0) ? "-" : "+", s.tree) : null)).filter(Boolean));
    } else {
      const why = sides.every((s) => s.ok) && sides.length === 2 && sides[0].tree === sides[1].tree ? `removable discontinuity (hole): both one-sided limits equal ${toText(sides[0].tree)}` : `finite one-sided limits (${detail})`;
      rejected.push({ value: X.eq(X.sym(x), p.tree), reason: `not an asymptote: ${why}` });
      env.log.add({ rule: "analysis.asymptote.not-vertical", title: `No vertical asymptote at ${x} = ${toText(p.tree)}`, why: `${why[0].toUpperCase()}${why.slice(1)}.`, kind: "note" });
    }
  }
  // periodic families of poles
  if (d.families.length) {
    const per = periodOf(f, x);
    if (!per) throw fail("infinitely many vertical asymptote candidates, but f is not periodic in a supported way");
    for (const fm of d.families) {
      const ratio = dv(per) / fm.p;
      if (Math.abs(ratio - Math.round(ratio)) > 1e-9) throw fail("the excluded points do not repeat with the period of f");
      // every member within one period of f
      for (let j = 0; j < Math.round(ratio); j++) {
        const a = tidy(C(X.add(fm.offset, X.mul(X.num(Q.Q(BigInt(j))), fm.period))));
        const L = limOf(f, x, a, "-"), R = limOf(f, x, a, "+");
        if (!L.ok || !R.ok) { partial = true; notes.push(`the behaviour near ${x} = ${toText(a)} could not be determined`); continue; }
        if (!(L.inf || R.inf)) { rejected.push({ value: X.eq(X.sym(x), a), reason: "not an asymptote: finite one-sided limits" }); continue; }
        const fam = C(X.add(a, X.mul(per, X.sym("k"))));
        answers.push({ kind: "general", label: "Vertical asymptote", tree: X.eq(X.sym(x), fam), param: "k", detail: `f -> ${toText(L.tree)} as ${x} -> ${toText(a)}-; f -> ${toText(R.tree)} as ${x} -> ${toText(a)}+ (and the same at every ${toText(a)} + k*${toText(per)}, since f has period ${toText(per)})` });
        checks.push(() => [-1, 0, 1].flatMap((k) => { const ak = C(X.add(a, X.mul(X.num(k), per))); return [sequenceCheck(f0, x, ak, "-", L.tree), sequenceCheck(f0, x, ak, "+", R.tree)]; }));
      }
    }
  }
  // horizontal / oblique at +oo and -oo
  const upper = d.ivs.some((iv) => iv.hi === null), lower = d.ivs.some((iv) => iv.lo === null);
  const rational = rationalParts(f, x);
  const far = [];
  // a periodic, non-constant f has no limit at +-oo (it takes two different values in every period)
  const per0 = periodOf(f, x);
  let periodicNoLimit = false;
  if (per0 && upper && lower) {
    const P0 = dv(per0), vals = [0.1, 0.37, 0.71].map((t) => t * P0).filter((t) => definedNum(f, x, t)).map((t) => fAt(f, x, t));
    if (vals.length >= 2 && Math.max(...vals) - Math.min(...vals) > 1e-6 * Math.max(1, ...vals.map(Math.abs))) {
      periodicNoLimit = true;
      checks.push(() => { const T = 1000 * P0 + 0.1 * P0, v1 = fAt(f0, x, T), v2 = fAt(f0, x, T + 0.27 * P0), v3 = fAt(f0, x, -T), v4 = fAt(f0, x, -T + 0.27 * P0);
        return [[v1, v2], [v3, v4]].map(([p, q]) => (Number.isFinite(p) && Number.isFinite(q) && Math.abs(p - q) > 1e-6 ? pass("oscillation", `f keeps taking different values (${fmt(p)}, ${fmt(q)}) far out`) : bad("oscillation", "f seems to settle far out"))); });
      notes.push(`f is periodic (period ${toText(per0)}) and not constant, so it has no limit as ${x} -> +-oo (no horizontal or oblique asymptote)`);
    }
  }
  for (const [to, has, name] of [[X.OO, upper, "oo"], [NEG_OO, lower, "-oo"]]) {
    if (!has || periodicNoLimit) continue;
    const L = limOf(f, x, to, "");
    if (!L.ok) {
      if (L.dne) { notes.push(`f has no limit as ${x} -> ${name} (no horizontal asymptote there)`); if (d.families.length) continue; }
      else { partial = true; notes.push(`the behaviour as ${x} -> ${name} could not be determined`); }
      continue;
    }
    if (!L.inf) { far.push({ name, kind: "Horizontal asymptote", line: L.tree, m: X.ZERO, b: L.tree, to }); continue; }
    const M = limOf(C(X.div(f, X.sym(x))), x, to, "");
    if (!M.ok || M.inf || M.tree === X.ZERO) {
      notes.push(`f grows faster or slower than linearly as ${x} -> ${name} (no oblique asymptote)`);
      if (!M.ok) partial = true;
      else if (M.inf) checks.push(() => [sequenceCheck(C(X.div(f0, X.sym(x))), x, to, "", M.tree), sequenceCheck(f0, x, to, "", L.tree)]);
      else checks.push(() => [sequenceCheck(C(X.div(f0, X.sym(x))), x, to, "", X.ZERO), sequenceCheck(f0, x, to, "", L.tree)]);
      continue;
    }
    const B = limOf(C(X.sub(f, X.mul(M.tree, X.sym(x)))), x, to, "");
    if (!B.ok || B.inf) {
      notes.push(`f - ${toText(M.tree)}${x} has no finite limit as ${x} -> ${name} (no oblique asymptote)`);
      if (B.ok) checks.push(() => [sequenceCheck(C(X.sub(f0, X.mul(M.tree, X.sym(x)))), x, to, "", B.tree)]); else partial = true;
      continue;
    }
    far.push({ name, kind: "Oblique asymptote", line: C(X.add(X.mul(M.tree, X.sym(x)), B.tree)), m: M.tree, b: B.tree, to });
  }
  if (rational) {
    env.log.add({ rule: "analysis.asymptote.division", title: "Polynomial division", why: `f = ${toText(rational.q)} + (${toText(rational.r)})/(${toText(rational.den)}); the remainder term tends to 0 as ${x} -> +-oo, so the graph approaches y = ${toText(rational.q)} when the quotient has degree at most 1.`, before: f, after: X.add(rational.q, X.div(rational.r, rational.den)) });
    for (const a of far) if (!safe(() => isZeroExact(X.sub(a.line, rational.q)))) throw fail(`the polynomial division (${toText(rational.q)}) and the limit ${toText(a.line)} disagree`);
    if (far.length && safe(() => isZeroExact(rational.r))) {
      // no remainder: the graph IS the line (minus any holes); a line is not an asymptote of itself
      const line = rational.q;
      rejected.push({ value: X.eq(X.sym(Y(x)), line), line: true, reason: `the graph of f is the line y = ${toText(line)} itself (apart from removable holes), so it is not an asymptote` });
      notes.push(`f equals ${toText(line)} wherever it is defined, so y = ${toText(line)} is the graph itself, not an asymptote`);
      far.length = 0;
    }
  }
  const yv = X.sym(Y(x));
  const merged = far.length === 2 && far[0].line === far[1].line ? [{ ...far[0], name: "+-oo", both: true }] : far;
  for (const a of merged) {
    answers.push({ kind: "exact", label: a.both || merged.length === 1 && far.length === 1 && !(upper && lower) ? a.kind : `${a.kind} (as ${x} -> ${a.name})`, tree: X.eq(yv, a.line), detail: `as ${x} -> ${a.name}` });
    env.log.add({ rule: a.kind === "Horizontal asymptote" ? "analysis.asymptote.horizontal" : "analysis.asymptote.oblique", title: `${a.kind} y = ${toText(a.line)}`, why: a.kind === "Horizontal asymptote" ? `lim f = ${toText(a.line)} as ${x} -> ${a.name}.` : `m = lim f/${x} = ${toText(a.m)} and b = lim (f - m ${x}) = ${toText(a.b)} as ${x} -> ${a.name}.`, before: null, after: X.eq(yv, a.line) });
    const targets = a.both ? [X.OO, NEG_OO] : [a.to];
    checks.push(() => targets.map((to) => sequenceCheck(C(X.sub(f0, a.line)), x, to, "", X.ZERO)));
  }
  if (notes.length) note(env, "analysis.asymptote.notes", "Notes", notes.join("; ") + ".");
  if (!answers.length) answers.push({ kind: "none", label: partial ? "No asymptote could be established" : "No asymptotes", proof: rejected.map((r) => `${toText(r.value)}: ${r.reason}`).join("; ") || "f has no infinite one-sided limits and no finite or linear behaviour at infinity" });
  return {
    answers, rejected, solutionStatus: partial ? "partial" : "exact", note: notes.join("; "), graph: { exprs: [f0], marks: [] },
    verify: () => {
      const res = checks.flatMap((c) => c());
      // rejected points: f stays bounded near them
      for (const r of rejected) {
        if (r.line) {
          const pts = [-7.3, -2.1, 0.37, 3.3, 11.9].filter((t) => definedNum(f0, x, t));
          const same = pts.length >= 3 && pts.every((t) => Math.abs(fAt(f0, x, t) - fAt(r.value.args[1], x, t)) <= 1e-9 * scale(fAt(f0, x, t)));
          res.push(same ? pass("coincides", `f equals ${toText(r.value.args[1])} at ${pts.length} sample points`) : bad("coincides", "f differs from the line"));
          continue;
        }
        const a = dv(r.value.args[1]);
        const vals = [1e-4, 1e-6, 1e-8].flatMap((h) => [fAt(f0, x, a - h * scale(a)), fAt(f0, x, a + h * scale(a))]).filter(Number.isFinite);
        const bounded = vals.length && Math.max(...vals.map(Math.abs)) < 1e6;
        res.push(bounded ? pass("bounded", `f stays bounded near ${x} = ${toText(r.value.args[1])}`) : bad("bounded", `f is large near ${x} = ${toText(r.value.args[1])}; it may be an asymptote`));
      }
      if (!res.length) res.push(open("asymptotes", "nothing to check numerically"));
      return TCV(res);
    },
  };
}
function rationalParts(f, x) {
  return safe(() => {
    const [n, d] = P.numDen(f);
    if (X.freeOf(d, x)) return null;
    const pn = P.fromTree(n, x), pd = P.fromTree(d, x);
    if (!pn || !pd || !pn.length || !pd.length) return null;
    const { q, r } = P.divmod(pn, pd);
    if (q.length > 2) return null;
    return { q: C(P.toTree(q, x)), r: C(P.toTree(r, x)), den: C(P.toTree(pd, x)) };
  });
}

// ---------------------------------------------------------------- critical points / extrema
function windowArg(rest, env) {
  if (!rest.length) return null;
  if (rest.length !== 2) throw fail("give the interval as two numbers a, b");
  const a = constArg(rest[0], "the left end"), b = constArg(rest[1], "the right end");
  if (!(a.v < b.v)) throw fail("the interval needs a < b");
  return { lo: a.tree, hi: b.tree, loOpen: false, hiOpen: false };
}
const pointTree = (p, value) => X.tuple(p.tree, value || X.num(Q.fromDecimal(String(+p.valueV.toPrecision(15)))));
function periodicFilter(res) {
  if (!res.period || !res.win || !res.win.periodic) return (c) => true;
  const P0 = dv(res.period);
  return (c) => c.v >= -P0 / 2 - 1e-12 && c.v < P0 / 2 - 1e-12;
}
// Points of one kind in a period window [-P/2, P/2), equally spaced by P/n with n points, form one
// family offset + k*(P/n) (for example 2k*pi - pi/2 and 2k*pi + pi/2 -> k*pi + pi/2). Returns
// [{ pts, offset, period }] groups; unmergeable points keep period P.
function periodGroups(res, pts) {
  const P = res.period, Pv = dv(P), n = pts.length;
  if (n >= 2 && pts.every((p) => !p.approx)) {
    const sorted = pts.slice().sort((a, b) => a.v - b.v), step = C(X.div(P, X.num(n)));
    const ok = sorted.every((p, i) => i === 0 || safe(() => isZeroExact(X.sub(X.sub(p.tree, sorted[i - 1].tree), step))));
    if (ok && Math.abs(sorted[0].v + Pv - sorted[n - 1].v - dv(step)) < 1e-9 * Math.max(1, Pv)) {
      const first = sorted.reduce((a, b) => (Math.abs(b.v) < Math.abs(a.v) - 1e-12 || (Math.abs(Math.abs(b.v) - Math.abs(a.v)) < 1e-12 && b.v > a.v) ? b : a));
      return [{ pts: sorted, offset: first.tree, period: step, rep: first }];
    }
  }
  return pts.map((p) => ({ pts: [p], offset: p.tree, period: P, rep: p }));
}
const famOf = (g) => C(X.add(g.offset, X.mul(g.period, X.sym("k"))));
function famTree(res, t) { return res.win && res.win.periodic ? C(X.add(t, X.mul(res.period, X.sym("k")))) : t; }

export function cmdCritical(node, env) {
  const { f, x, rest } = fnAndVar(node.args, "critical");
  const res = analyze(f, x, env, { window: windowArg(rest, env) });
  const keep = periodicFilter(res);
  const cps = res.crit.filter(keep);
  env.log.add({ rule: "analysis.critical.derivative", title: "Differentiate", why: "Critical points are the points of the domain where f' = 0 or f' is undefined.", before: res.f, after: res.df });
  const periodic = !!(res.win && res.win.periodic);
  const lab = (c) => (c.stationary ? "Critical point (f' = 0)" : "Critical point (f' undefined)");
  const answers = periodic && !cps.some((c) => c.approx)
    ? [true, false].flatMap((st) => periodGroups(res, cps.filter((c) => !!c.stationary === st)).map((g) => ({ kind: "general", label: lab(g.rep), tree: famOf(g), param: "k" })))
    : cps.map((c) => {
      const label = lab(c);
      if (c.approx) return { kind: "approx", label, approx: c.approx, value: c.valueV };
      return periodic ? { kind: "general", label, tree: famTree(res, c.tree), param: "k", value: c.value } : { kind: "exact", label, tree: c.tree, value: c.value, approx: X.isNum(c.tree) ? undefined : safe(() => approxRec(c.tree, 20)) };
    });
  if (!answers.length) answers.push({ kind: "none", label: "No critical points", proof: `f'(${x}) = ${toText(res.df)} is never 0 and is defined on the whole domain` });
  note(env, "analysis.critical.list", "Critical points", answers.map((a) => `${a.label}: ${a.tree ? toText(a.tree) : a.approx ? a.approx.value : ""}`).join("; ") + (periodic ? ` (k any integer; f has period ${toText(res.period)})` : "") + ".");
  return {
    answers, solutionStatus: cps.some((c) => c.approx) ? "approximate" : "exact", conditions: periodic ? [] : [],
    graph: { exprs: [f], marks: cps.map((c) => ({ x: c.v, y: c.valueV, label: "critical point", kind: "critical" })) },
    verify: () => TCV(cps.length ? cps.map((c) => verifyCritical(f, x, c)) : [verifyNoCritical(res)]),
  };
}
function verifyCritical(f, x, c) {
  if (c.stationary) {
    const d = numDeriv(f, x, c.v);
    // one-sided quotients too (Richardson-extrapolated), so a symmetric corner such as |x| at 0 cannot pass
    const fv0 = fAt(f, x, c.v), h0 = 1e-4 * scale(c.v);
    const one = (s) => { const q = (hh) => (fAt(f, x, c.v + s * hh) - fv0) / (s * hh); return 2 * q(h0 / 2) - q(h0); };
    const sides = [one(1), one(-1)];
    const ok = Math.abs(d.value) <= 1e-5 * Math.max(1, Math.abs(fv0)) && sides.every((q) => Number.isFinite(q) && Math.abs(q) <= 1e-4 * Math.max(1, Math.abs(fv0)));
    return ok ? pass("derivative", `numerical f'(${fmt(c.v)}) = ${d.value.toExponential(1)} (zero)`) : bad("derivative", `numerical f'(${fmt(c.v)}) = ${fmt(d.value)} is not zero`);
  }
  const h = [1e-4, 1e-6].map((e) => e * scale(c.v));
  const fv = fAt(f, x, c.v);
  const qs = h.flatMap((hh) => [(fAt(f, x, c.v + hh) - fv) / hh, (fv - fAt(f, x, c.v - hh)) / hh]);
  const fin = qs.filter(Number.isFinite);
  const spread = fin.length ? Math.max(...fin) - Math.min(...fin) : Infinity;
  const blowup = fin.some((q) => Math.abs(q) > 1e2);
  return (spread > 1e-2 || blowup || fin.length < qs.length) ? pass("not differentiable", `difference quotients at ${fmt(c.v)} disagree or blow up (${fin.map(fmt).join(", ")})`) : bad("not differentiable", `f looks differentiable at ${fmt(c.v)}`);
}
function verifyNoCritical(res) {
  const { f0: f, x } = res;
  let n = 0;
  for (const t of domainSamples(res, 400)) {
    const d = numDeriv(f, x, t);
    if (!Number.isFinite(d.value)) continue;
    const s = res.c1.charts.find((ch) => t > ch.comp.lo.v && t < ch.comp.hi.v);
    if (!s) continue;
    if (Math.abs(d.value) < 1e-9) continue;
    if (Math.sign(d.value) !== s.signs[0]) return bad("derivative sign", `f' changes sign near ${fmt(t)}`);
    n++;
  }
  return pass("derivative sign", `numerical f' keeps one sign on each piece of the domain (${n} points)`);
}

export function cmdExtrema(node, env) {
  const { f, x, rest } = fnAndVar(node.args, "extrema");
  const win = windowArg(rest, env);
  const res = analyze(f, x, env, { window: win });
  const periodic = !!(res.win && res.win.periodic);
  const keep = periodicFilter(res);
  env.log.add({ rule: "analysis.extrema.derivative", title: "Differentiate", why: "Local extrema can only occur where f' = 0 or f' is undefined.", before: res.f, after: res.df });
  let d2 = null;
  try { d2 = C(diff(res.df, x)); } catch (_) { d2 = null; }
  const signTxt = (s) => (s > 0 ? "+" : s < 0 ? "-" : "0");
  const crit = res.crit.filter(keep);
  note(env, "analysis.extrema.sign-chart", "Sign of f' around each critical point", crit.length ? crit.map((c) => {
    let second = "";
    if (d2 && c.stationary && !c.approx) { const s2 = safe(() => C(X.subs(d2, { [x]: c.tree }))); if (s2 && X.freeSymbols(s2).size === 0 && s2 !== X.UNDEF) second = `; f''(${toText(c.tree)}) = ${toText(s2)}`; }
    return `at ${x} = ${ptText(c)}: f' goes ${signTxt(c.sL)} to ${signTxt(c.sR)}, so ${c.type === "max" ? "local maximum" : c.type === "min" ? "local minimum" : "no extremum"}${second}`;
  }).join("; ") + "." : "There are no critical points.");
  // absolute extrema from the images of the domain components (in the window)
  const im = images(res);
  const recs = im.parts.flatMap((p) => [p.lo, p.hi]);
  const maxRec = recs.reduce((a, b) => { const c = cmpRec(b, a); return c > 0 || (c === 0 && b.attained && !a.attained) ? b : a; });
  const minRec = recs.reduce((a, b) => { const c = cmpRec(b, a); return c < 0 || (c === 0 && b.attained && !a.attained) ? b : a; });
  const absMax = maxRec.attained ? maxRec : null;
  const absMin = minRec.attained ? minRec : null;
  const sameVal = (a, b) => a && b && cmpRec(a, b) === 0;
  const answers = [];
  const marks = [];
  const used = new Set();
  const pushPt = (label, c, isPeriodic) => {
    const tree = isPeriodic ? X.tuple(famTree(res, c.tree), c.value) : pointTree(c, c.value);
    if (c.approx) answers.push({ kind: "approx", label, approx: c.approx, value: c.valueV, note: `${x} ~ ${c.approx.value}, f ~ ${fmt(c.valueV)}` });
    else answers.push({ kind: isPeriodic ? "general" : "exact", label, tree, ...(isPeriodic ? { param: "k" } : {}), x: c.tree, value: c.value });
    marks.push({ x: c.v, y: c.valueV, label, kind: "extremum" });
  };
  for (const c of crit) {
    if (c.type === "none") continue;
    const isAbs = c.type === "max" ? sameVal(absMax, { tree: c.value, v: c.valueV, attained: true }) : sameVal(absMin, { tree: c.value, v: c.valueV, attained: true });
    const label = `Local ${isAbs ? "and absolute " : ""}${c.type === "max" ? "maximum" : "minimum"}`;
    pushPt(label, c, periodic);
    used.add(c.v);
  }
  // absolute extrema attained at ends of the window / domain (not interior critical points)
  const endPts = [];
  for (const p of im.parts) for (const side of ["lo", "hi"]) {
    const e = p.comp[side];
    if (e.open || !e.tree) continue;
    const v = valueAt(res.f0, x, e.tree);
    if (v === null) continue;
    endPts.push({ tree: e.tree, v: e.v, value: v, valueV: dv(v) });
  }
  if (!periodic) for (const [rec, kind] of [[absMax, "maximum"], [absMin, "minimum"]]) {
    if (!rec) continue;
    for (const e of endPts) {
      if (used.has(e.v) || !sameVal({ tree: e.value, v: e.valueV, attained: true }, rec)) continue;
      pushPt(`Absolute ${kind} (endpoint)`, e, false);
      used.add(e.v);
    }
    // an absolute extremum at a critical point that is not a local one in the two-sided sense cannot happen inside a component
  }
  const absNotes = [];
  if (!absMax) absNotes.push(`no absolute maximum (${maxRec.inf ? "f is unbounded above" : `f approaches ${toText(maxRec.tree)} but never attains it`})`);
  if (!absMin) absNotes.push(`no absolute minimum (${minRec.inf ? "f is unbounded below" : `f approaches ${toText(minRec.tree)} but never attains it`})`);
  if (periodic) absNotes.push(`f has period ${toText(res.period)}; k is any integer`);
  if (absNotes.length) note(env, "analysis.extrema.absolute", "Absolute extrema", absNotes.join("; ") + ".");
  if (!answers.length) answers.push({ kind: "none", label: "No extrema", proof: crit.length ? `f' does not change sign at ${crit.map((c) => ptText(c)).join(", ")}` : "f has no critical points and no attained extreme values" });
  const where = win ? `[${toText(win.lo)}, ${toText(win.hi)}]` : null;
  return {
    answers, solutionStatus: answers.some((a) => a.kind === "approx") ? "approximate" : "exact",
    note: [where ? `on the interval ${where}` : "", ...absNotes].filter(Boolean).join("; "),
    extra: { absolute: { max: absMax ? absMax.tree : null, min: absMin ? absMin.tree : null }, notes: absNotes },
    graph: { exprs: [f], marks },
    verify: () => TCV(verifyExtrema(res, crit, answers, absMax, absMin)),
  };
}
function cmpRec(a, b) {
  if (a.inf || b.inf) return (a.inf || 0) === (b.inf || 0) ? 0 : (a.inf || 0) < (b.inf || 0) ? -1 : 1;
  if (Math.abs(a.v - b.v) > 1e-9 * Math.max(1, Math.abs(a.v), Math.abs(b.v))) return a.v < b.v ? -1 : 1;
  if (a.tree === b.tree || a.approx || b.approx) return 0;
  const s = safe(() => C(X.sub(a.tree, b.tree)));
  if (s === X.ZERO) return 0;
  const h = s && safe(() => hp(s, 40));
  return h && h.ok && Math.abs(h.re) > 1e-30 ? (h.re > 0 ? 1 : -1) : 0;
}
function verifyExtrema(res, crit, answers, absMax, absMin) {
  const { f0: f, x } = res;
  const out = [];
  for (const c of crit) {
    const fv = fAt(f, x, c.v);
    if (!c.approx && Math.abs(fv - c.valueV) > 1e-8 * scale(fv)) return [bad("value", `f(${ptText(c)}) = ${fmt(fv)}, not ${fmt(c.valueV)}`)];
    const near = [1e-2, 1e-3, 1e-4, 1e-5].flatMap((h) => [c.v - h * scale(c.v), c.v + h * scale(c.v)]).filter((t) => t > c.comp.lo.v && t < c.comp.hi.v);
    const vals = near.map((t) => [t, fAt(f, x, t)]).filter(([, v]) => Number.isFinite(v));
    const tol = 1e-12 * scale(fv);
    if (c.type === "max" && vals.some(([, v]) => v > fv + tol)) return [bad("local", `f is larger near ${ptText(c)}; not a local maximum`)];
    if (c.type === "min" && vals.some(([, v]) => v < fv - tol)) return [bad("local", `f is smaller near ${ptText(c)}; not a local minimum`)];
    if (c.type === "none") {
      const left = vals.filter(([t]) => t < c.v).map(([, v]) => v - fv), right = vals.filter(([t]) => t > c.v).map(([, v]) => v - fv);
      const isExt = (left.every((d) => d < -tol) && right.every((d) => d < -tol)) || (left.every((d) => d > tol) && right.every((d) => d > tol));
      if (isExt && left.length && right.length) return [bad("local", `f looks like it has an extremum at ${ptText(c)}`)];
      out.push(pass("not an extremum", `f takes values on both sides of f(${ptText(c)}) nearby`));
      continue;
    }
    out.push(pass("local", `f(${ptText(c)}) = ${fmt(fv)} is ${c.type === "max" ? "not exceeded" : "not undercut"} at ${vals.length} nearby points`));
  }
  // absolute: dense sampling of the whole window / domain
  const samples = domainSamples(res, 3000).filter((t) => definedNum(f, x, t)).map((t) => fAt(f, x, t));
  if (absMax) { const m = Math.max(...samples); if (m > absMax.v + 1e-9 * scale(absMax.v)) return [bad("absolute", `f reaches ${fmt(m)} > ${fmt(absMax.v)}`)]; out.push(pass("absolute max", `no sampled value (${samples.length} points) exceeds ${fmt(absMax.v)}`)); }
  if (absMin) { const m = Math.min(...samples); if (m < absMin.v - 1e-9 * scale(absMin.v)) return [bad("absolute", `f reaches ${fmt(m)} < ${fmt(absMin.v)}`)]; out.push(pass("absolute min", `no sampled value (${samples.length} points) is below ${fmt(absMin.v)}`)); }
  if (!out.length) out.push(pass("sample", "no critical points to check"));
  return out;
}

// ---------------------------------------------------------------- inflection points
export function cmdInflection(node, env) {
  const { f, x, rest } = fnAndVar(node.args, "inflection");
  const res = analyze(f, x, env, { window: windowArg(rest, env) });
  const periodic = !!(res.win && res.win.periodic);
  const keep = periodicFilter(res);
  const pts = inflections(res).filter(keep);
  env.log.add({ rule: "analysis.inflection.second", title: "Second derivative", why: "Concavity can change only where f'' = 0 or f'' is undefined; an inflection point needs a sign change of f'' and f defined there.", before: res.df, after: res.d2 });
  // periodic: merge equally spaced points that share one value (sin: k*pi, value 0)
  const byValue = [];
  for (const p of pts) { const g = byValue.find((q) => !p.approx && !q[0].approx && safe(() => isZeroExact(X.sub(q[0].value, p.value)))); if (g) g.push(p); else byValue.push([p]); }
  const answers = periodic && !pts.some((p) => p.approx)
    ? byValue.flatMap((grp) => periodGroups(res, grp).map((g) => ({ kind: "general", label: "Inflection point", tree: X.tuple(famOf(g), g.rep.value), param: "k" })))
    : pts.map((p) => (p.approx ? { kind: "approx", label: "Inflection point", approx: p.approx, value: fAt(f, x, p.v) }
      : periodic ? { kind: "general", label: "Inflection point", tree: X.tuple(famTree(res, p.tree), p.value), param: "k" } : { kind: "exact", label: "Inflection point", tree: X.tuple(p.tree, p.value) }));
  note(env, "analysis.inflection.chart", "Sign of f''", pts.length ? pts.map((p) => `f'' changes sign at ${x} = ${ptText(p)}`).join("; ") + "." : "f'' does not change sign on the domain.");
  if (!answers.length) answers.push({ kind: "none", label: "No inflection points", proof: "f'' does not change sign on any piece of the domain" });
  return {
    answers, solutionStatus: pts.some((p) => p.approx) ? "approximate" : "exact",
    graph: { exprs: [f], marks: pts.map((p) => ({ x: p.v, y: fAt(f, x, p.v), label: "inflection", kind: "inflection" })) },
    verify: () => TCV(pts.length ? pts.map((p) => verifyInflection(f, x, p)) : [verifyNoInflection(res)]),
  };
}
// no inflection claimed: numerical second differences of the original f keep one sign on each piece
function verifyNoInflection(res) {
  const { f0: f, x } = res;
  let n = 0;
  for (const comp of res.comps) {
    const lo = Number.isFinite(comp.lo.v) ? comp.lo.v : Math.min(-30, comp.hi.v - 30), hi = Number.isFinite(comp.hi.v) ? comp.hi.v : Math.max(30, lo + 60);
    let seen = 0;
    for (let i = 1; i < 120; i++) {
      const t = lo + ((hi - lo) * i) / 120, h = Math.min(1e-2, (hi - lo) / 1000) * scale(t);
      const v = secondDiff(f, x, t, h);
      const tol = (64 * 2.2e-16 * scale(fAt(f, x, t))) / (h * h) + 1e-9;
      if (!Number.isFinite(v) || Math.abs(v) <= tol) continue;
      const sg = Math.sign(v);
      if (seen && sg !== seen) return bad("concavity", `numerical f'' changes sign near ${x} = ${fmt(t)}`);
      seen = sg; n++;
    }
  }
  return n >= 20 ? pass("concavity", `numerical second differences keep one sign on each piece of the domain (${n} points)`) : open("concavity", "too few sample points");
}
function secondDiff(f, x, t, h) { return (fAt(f, x, t + h) - 2 * fAt(f, x, t) + fAt(f, x, t - h)) / (h * h); }
function verifyInflection(f, x, p) {
  const room = Math.min(p.v - p.comp.lo.v, p.comp.hi.v - p.v, 1) / 4;
  for (const frac of [0.5, 0.1, 0.02]) {
    const dlt = room * frac, h = dlt / 8;
    const a = secondDiff(f, x, p.v - dlt, h), b = secondDiff(f, x, p.v + dlt, h);
    if (!Number.isFinite(a) || !Number.isFinite(b) || Math.sign(a) !== p.sL || Math.sign(b) !== p.sR) return bad("concavity", `numerical f'' near ${ptText(p)} is ${fmt(a)} (left) and ${fmt(b)} (right)`);
  }
  const fv = fAt(f, x, p.v);
  if (!Number.isFinite(fv)) return bad("defined", `f is undefined at ${ptText(p)}`);
  return pass("concavity", `numerical second differences change sign across ${x} = ${ptText(p)} (${p.sL > 0 ? "up to down" : "down to up"})`);
}

// ---------------------------------------------------------------- monotonicity / concavity
export function cmdMonotonic(node, env) {
  const { f, x, rest } = fnAndVar(node.args, "monotonic");
  const res = analyze(f, x, env, { window: windowArg(rest, env) });
  const periodic = !!(res.win && res.win.periodic);
  const clip = periodic ? { lo: X.ZERO, hi: res.period, a: 0, b: dv(res.period) } : null;
  const toIvs = (pieces, s) => pieces.filter((p) => p.sign === s).map((p) => {
    let lo = p.lo.tree, hi = p.hi.tree, lv = p.lo.v, hv = p.hi.v;
    if (clip) { if (hv <= clip.a || lv >= clip.b) return null; if (lv < clip.a) { lo = clip.lo; lv = clip.a; } if (hv > clip.b) { hi = clip.hi; hv = clip.b; } }
    return { lo: Number.isFinite(lv) ? lo : null, hi: Number.isFinite(hv) ? hi : null, loOpen: true, hiOpen: true, lv, hv };
  }).filter(Boolean).filter((iv) => iv.hv > iv.lv);
  const m = monotonePieces(res);
  const inc = toIvs(m, 1), dec = toIvs(m, -1), cst = toIvs(m, 0);
  env.log.add({ rule: "analysis.monotonic.derivative", title: "Sign of f'", why: "f increases where f' > 0 and decreases where f' < 0; f' can change sign only at its zeros and where it is undefined.", before: res.f, after: res.df });
  const suffix = periodic ? ` on [0, ${toText(res.period)}] (the pattern repeats with period ${toText(res.period)})` : "";
  const answers = [];
  const mk = (label, ivs) => answers.push({ kind: "set", label: label + suffix, variable: x, tree: ivs.length ? setTree(ivs, x, { contractNe: false }) : X.set(), interval: ivOut(ivs), text: ivs.length ? ivsText(ivs) : "nowhere" });
  mk("Increasing", inc); mk("Decreasing", dec);
  if (cst.length) mk("Constant", cst);
  let up = [], down = [], concNote = "";
  try {
    const c2 = secondChart(res);
    if (!c2.constantZero) {
      const m2 = monotonePieces(res, c2);
      up = toIvs(m2, 1); down = toIvs(m2, -1);
      mk("Concave up", up); mk("Concave down", down);
      env.log.add({ rule: "analysis.monotonic.concavity", title: "Sign of f''", why: "f is concave up where f'' > 0 and concave down where f'' < 0.", before: res.df, after: res.d2 });
    } else concNote = "f'' = 0: f is linear on each piece (no concavity)";
  } catch (e) { if (!e || e.code !== "UNSUPPORTED") throw e; concNote = `concavity not determined (${e.message})`; }
  if (concNote) note(env, "analysis.monotonic.concavity-note", "Concavity", concNote + ".");
  note(env, "analysis.monotonic.result", "Intervals", `increasing on ${ivsText(inc)}; decreasing on ${ivsText(dec)}${suffix}. Each interval is stated as open; f is monotone on each interval separately (not necessarily on their union).`);
  return {
    answers, solutionStatus: "exact", note: concNote,
    graph: { exprs: [f], marks: [] },
    verify: () => TCV([...verifyMono(f, x, inc, 1), ...verifyMono(f, x, dec, -1), ...verifyConc(f, x, up, 1), ...verifyConc(f, x, down, -1)]),
  };
}
function sampleIv(iv, n = 16) {
  const a = Number.isFinite(iv.lv) ? iv.lv : (Number.isFinite(iv.hv) ? iv.hv : 0) - 60;
  const b = Number.isFinite(iv.hv) ? iv.hv : a + 60 + (Number.isFinite(iv.lv) ? 0 : 60);
  const pts = [];
  for (let i = 1; i < n; i++) pts.push(a + ((b - a) * i) / n);
  return pts;
}
function verifyMono(f, x, ivs, s) {
  return ivs.map((iv) => {
    const pts = sampleIv(iv);
    const vals = pts.map((t) => fAt(f, x, t));
    for (let i = 1; i < vals.length; i++) {
      const dlt = (vals[i] - vals[i - 1]) * s;
      if (!Number.isFinite(dlt) || dlt < -1e-12 * scale(vals[i])) return bad("monotone", `f(${fmt(pts[i - 1])}) = ${fmt(vals[i - 1])} and f(${fmt(pts[i])}) = ${fmt(vals[i])} contradict ${s > 0 ? "increasing" : "decreasing"} on ${ivText2(iv)}`);
    }
    return pass("monotone", `f is ${s > 0 ? "increasing" : "decreasing"} along ${pts.length} points of ${ivText2(iv)}`);
  });
}
function verifyConc(f, x, ivs, s) {
  return ivs.map((iv) => {
    const pts = sampleIv(iv, 10);
    const w = (pts[1] - pts[0]) / 20;
    for (const t of pts) {
      const d2 = secondDiff(f, x, t, w);
      if (!Number.isFinite(d2)) continue;
      const tol = (64 * 2.2e-16 * Math.max(1, Math.abs(fAt(f, x, t)))) / (w * w) + 1e-12;
      if (d2 * s < -tol) return bad("concavity", `numerical f''(${fmt(t)}) = ${fmt(d2)} contradicts concave ${s > 0 ? "up" : "down"}`);
    }
    return pass("concavity", `second differences have the claimed sign along ${ivText2(iv)}`);
  });
}
const ivText2 = (iv) => `(${Number.isFinite(iv.lv) ? fmt(iv.lv) : "-oo"}, ${Number.isFinite(iv.hv) ? fmt(iv.hv) : "oo"})`;

// ---------------------------------------------------------------- tangent / normal
export function cmdTangentNormal(which) {
  return (node, env) => {
    let args = node.args;
    if (args.length === 2 && args[1].k === "eq" && args[1].args[0].k === "sym") args = [args[0], args[1].args[0], args[1].args[1]];
    const { f, x, rest } = fnAndVar(args, which);
    if (rest.length !== 1) throw fail(`${which} needs the point: ${which}(f, x, a)`);
    const a = constArg(rest[0], "the point");
    const fa = valueAt(f, x, a.tree);
    if (fa === null) throw fail(`f is not defined at ${x} = ${toText(a.tree)}, so there is no ${which} line there`);
    const fs = C(f);
    const df = C(diff(fs, x));
    const X0 = X.sym(x), yv = X.sym(Y(x));
    let m = valueAt(df, x, a.tree);
    let vertical = false, corner = null;
    if (m === null) {
      // not differentiable by formula: one-sided limits of f' decide (vertical tangent or corner)
      const L = limOf(df, x, a.tree, "-"), R = limOf(df, x, a.tree, "+");
      const Lv = L.ok ? L : null, Rv = R.ok ? R : null;
      if ((Lv && Lv.inf) || (Rv && Rv.inf)) {
        if (Lv && Rv && Lv.inf && Rv.inf && Lv.inf !== Rv.inf) corner = `f' -> ${toText(Lv.tree)} from the left and ${toText(Rv.tree)} from the right (a cusp)`;
        else vertical = true;
      } else if (Lv && Rv && !Lv.inf && !Rv.inf && Lv.tree !== Rv.tree) corner = `the one-sided derivatives are ${toText(Lv.tree)} and ${toText(Rv.tree)} (a corner)`;
      else throw fail(`the derivative at ${x} = ${toText(a.tree)} could not be determined`);
    }
    // differentiable point: check the formula derivative is really the limit (removable cases)
    env.log.add({ rule: "analysis.tangent.value", title: `Point of tangency`, why: `f(${toText(a.tree)}) = ${toText(fa)}.`, before: f, after: fa });
    if (corner) {
      note(env, "analysis.tangent.corner", "Not differentiable", `f is not differentiable at ${x} = ${toText(a.tree)}: ${corner}. There is no ${which} line.`);
      return { answers: [{ kind: "none", label: `No ${which} line: f is not differentiable at ${x} = ${toText(a.tree)}`, proof: corner }], solutionStatus: "exact", noSolution: true,
        verify: () => TCV([verifyCorner(f, x, a.v)]) };
    }
    if (vertical) {
      note(env, "analysis.tangent.vertical", "Vertical tangent", `f'(${x}) -> +-oo as ${x} -> ${toText(a.tree)} while f is continuous there, so the tangent line is vertical; its slope is undefined.`);
      const tan = X.eq(X0, a.tree), nor = X.eq(yv, fa);
      const answers = which === "tangent"
        ? [{ kind: "exact", label: "Tangent line (vertical)", tree: tan }, { kind: "none", label: "Slope: undefined (vertical tangent)" }]
        : [{ kind: "exact", label: "Normal line (horizontal)", tree: nor }, { kind: "exact", label: "Slope", tree: X.ZERO }];
      return { answers, solutionStatus: "exact", graph: { exprs: [f], marks: [{ x: a.v, y: dv(fa), label: "point", kind: "point" }] }, verify: () => TCV([verifyVertical(f, x, a.v)]) };
    }
    env.log.add({ rule: "analysis.tangent.slope", title: "Slope from the derivative", why: `f'(${x}) = ${toText(df)}, so the slope at ${x} = ${toText(a.tree)} is ${toText(m)}.`, before: df, after: m });
    let slope = m, line;
    if (which === "normal") {
      if (m === X.ZERO) {
        note(env, "analysis.normal.vertical", "Vertical normal", "The tangent is horizontal, so the normal line is vertical.");
        return { answers: [{ kind: "exact", label: "Normal line (vertical)", tree: X.eq(X0, a.tree) }, { kind: "none", label: "Slope: undefined (vertical normal)" }], solutionStatus: "exact",
          graph: { exprs: [f], marks: [{ x: a.v, y: dv(fa), label: "point", kind: "point" }] }, verify: () => TCV([verifySlope(f, x, a.v, 0)]) };
      }
      slope = tidy(C(X.div(X.NEG_ONE, m)));
      env.log.add({ rule: "analysis.normal.slope", title: "Normal slope", why: `The normal is perpendicular to the tangent: slope = -1/${toText(m)} = ${toText(slope)}.`, before: m, after: slope });
    }
    line = tidy(C(X.add(X.mul(slope, X.sub(X0, a.tree)), fa)));
    const eqn = X.eq(yv, line);
    env.log.add({ rule: "analysis.tangent.line", title: "Point-slope form", why: `y = m(x - a) + f(a) with m = ${toText(slope)}, a = ${toText(a.tree)}, f(a) = ${toText(fa)}.`, before: X.eq(yv, X.add(X.mul(slope, X.sub(X0, a.tree)), fa)), after: eqn });
    return {
      answers: [{ kind: "exact", label: which === "tangent" ? "Tangent line" : "Normal line", tree: eqn },
        ...((() => { const si = safe(() => C(expand(line))); return si && si !== line ? [{ kind: "exact", label: "Slope-intercept form", tree: X.eq(yv, si) }] : []; })()),
        { kind: "exact", label: "Slope", tree: slope }],
      solutionStatus: "exact", graph: { exprs: [f, line], marks: [{ x: a.v, y: dv(fa), label: "point", kind: "point" }] },
      verify: () => {
        const res = [verifySlope(f, x, a.v, dv(m))];
        const lv = fAt(line, x, a.v), fv = fAt(f, x, a.v);
        res.push(Math.abs(lv - fv) <= 1e-9 * scale(fv) ? pass("point", `the line passes through (${fmt(a.v)}, ${fmt(fv)})`) : bad("point", `the line misses f(${fmt(a.v)}) = ${fmt(fv)}`));
        const ls = (fAt(line, x, a.v + 1) - lv);
        const want = dv(slope);
        res.push(Math.abs(ls - want) <= 1e-9 * scale(want) ? pass("line slope", `the line's slope is ${fmt(ls)}`) : bad("line slope", `the line's slope is ${fmt(ls)}, expected ${fmt(want)}`));
        return TCV(res);
      },
    };
  };
}
function verifySlope(f, x, a, m) {
  const d = numDeriv(f, x, a);
  const ok = Number.isFinite(d.value) && Math.abs(d.value - m) <= 1e-6 * scale(m);
  return ok ? pass("central difference", `numerical f'(${fmt(a)}) = ${fmt(d.value)} matches the slope ${fmt(m)}`) : bad("central difference", `numerical f'(${fmt(a)}) = ${fmt(d.value)}, but the claimed slope is ${fmt(m)}`);
}
function verifyVertical(f, x, a) {
  const fa = fAt(f, x, a);
  const qs = [1e-2, 1e-4, 1e-6, 1e-8].map((h) => { h *= scale(a); const r = (fAt(f, x, a + h) - fa) / h, l = (fa - fAt(f, x, a - h)) / h; return [l, r]; });
  const mags = qs.map(([l, r]) => Math.max(Number.isFinite(l) ? Math.abs(l) : 0, Number.isFinite(r) ? Math.abs(r) : 0));
  const grows = mags.every((m, i) => i === 0 || m > mags[i - 1]) && mags[mags.length - 1] > 100;
  return grows ? pass("difference quotients", `difference quotients at ${fmt(a)} grow without bound (${mags.map(fmt).join(", ")})`) : bad("difference quotients", `difference quotients at ${fmt(a)} stay bounded (${mags.map(fmt).join(", ")})`);
}
function verifyCorner(f, x, a) {
  const fa = fAt(f, x, a);
  const h = 1e-6 * scale(a);
  const l = (fa - fAt(f, x, a - h)) / h, r = (fAt(f, x, a + h) - fa) / h;
  const differ = !(Number.isFinite(l) && Number.isFinite(r)) || Math.abs(l - r) > 1e-3 * Math.max(1, Math.abs(l), Math.abs(r));
  return differ ? pass("one-sided quotients", `left ${fmt(l)} and right ${fmt(r)} difference quotients differ`) : bad("one-sided quotients", `f looks differentiable at ${fmt(a)}`);
}

export { domainSamples };
