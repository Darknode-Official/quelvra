// Quelvra mistake detector.
//
// checkLines(lines, opts) takes a student's working, one line per step, and reports for each
// transition whether it keeps the math the same. The judgement uses the equivalence checker
// (exact simplification, then independent numeric probing), never text comparison.
// When a transition is wrong, `diagnose` tries a catalogue of classic mistakes by rewriting the
// previous line the wrong way and testing whether that reproduces the student's line.
//
// Result per transition:
//   { from, to, status: "ok" | "ok-conditional" | "wrong" | "unchecked", kind, message, diagnosis?, counterexample? }

import * as X from "./expr.js";
import * as N from "./num.js";
import { parse, parseDetailed } from "./parse.js";
import { simplify, expand, makeCtx } from "./simplify.js";
import { toText } from "./print.js";
import { equivalent, evalReal, truth } from "./verify.js";

const isRelation = (u) => u.k === "eq" || u.k === "rel" || u.k === "and" || u.k === "or";

function residual(u) {
  if (u.k === "eq" || u.k === "rel") return simplify(X.sub(u.args[0], u.args[1]));
  return null;
}

// Real roots of a single-variable expression on [lo, hi] (scan + bisection). Used only as an
// independent probe, never to answer the user's question.
function probeRoots(f, x, lo = -60, hi = 60, steps = 4800) {
  const roots = [];
  const F = (t) => evalReal(f, { [x]: t });
  let px = lo, pv = F(lo);
  for (let i = 1; i <= steps; i++) {
    const cx = lo + ((hi - lo) * i) / steps, cv = F(cx);
    if (Number.isFinite(pv) && Number.isFinite(cv)) {
      if (pv === 0) roots.push(px);
      else if (pv * cv < 0) {
        let a = px, b = cx, fa = pv;
        for (let k = 0; k < 80; k++) {
          const m = (a + b) / 2, fm = F(m);
          if (!Number.isFinite(fm)) break;
          if (fa * fm <= 0) b = m; else { a = m; fa = fm; }
        }
        const r = (a + b) / 2;
        // reject sign changes across poles: |f| must be small at the root
        if (Math.abs(F(r)) < 1e-6 * Math.max(1, Math.abs(pv), Math.abs(cv))) roots.push(r);
      }
    } else if (Number.isFinite(pv) && Math.abs(pv) < 1e-12) roots.push(px);
    px = cx; pv = cv;
  }
  // tangential roots (even multiplicity): local minima of |f| near zero
  for (let i = 1; i < steps; i++) {
    const a = lo + ((hi - lo) * (i - 1)) / steps, b = lo + ((hi - lo) * i) / steps, c = lo + ((hi - lo) * (i + 1)) / steps;
    const fa = Math.abs(F(a)), fb = Math.abs(F(b)), fc = Math.abs(F(c));
    if (fb < fa && fb < fc && fb < 1e-3) {
      // golden-section refine |f|
      let l = a, r = c;
      for (let k = 0; k < 80; k++) { const m1 = l + (r - l) * 0.382, m2 = l + (r - l) * 0.618; if (Math.abs(F(m1)) < Math.abs(F(m2))) r = m2; else l = m1; }
      const m = (l + r) / 2;
      if (Math.abs(F(m)) < 1e-9 && !roots.some((q) => Math.abs(q - m) < 1e-6)) roots.push(m);
    }
  }
  const out = [];
  for (const r of roots.sort((a, b) => a - b)) if (!out.length || Math.abs(out[out.length - 1] - r) > 1e-7 * Math.max(1, Math.abs(r))) out.push(r);
  return out;
}

// Compare two relations in one variable by their real solution sets (probed independently).
function compareRelations(a, b, vars) {
  if (vars.length !== 1) return compareMultivar(a, b, vars);
  const x = vars[0];
  if (a.k === "eq" && b.k === "eq") {
    const ra = residual(a), rb = residual(b);
    // proportional residuals (nonzero constant ratio) are equivalent: add/subtract/multiply both sides
    const ratio = simplify(X.div(ra, rb));
    if (X.freeOf(ratio, X.sym(x)) && X.isNum(ratio) && !X.isZero(ratio)) return { status: "ok", kind: "same-solutions" };
    const ta = probeRoots(ra, x), tb = probeRoots(rb, x);
    const inB = (t) => tb.some((q) => Math.abs(q - t) < 1e-6 * Math.max(1, Math.abs(t)));
    const inA = (t) => ta.some((q) => Math.abs(q - t) < 1e-6 * Math.max(1, Math.abs(t)));
    const lost = ta.filter((t) => !inB(t)), gained = tb.filter((t) => !inA(t));
    // also make sure the gained/lost points really are roots in the original relation (domain aware)
    const lostReal = lost.filter((t) => truth(a, { [x]: t }, "real", 1e-7) === true);
    const gainedReal = gained.filter((t) => truth(a, { [x]: t }, "real", 1e-7) !== true);
    if (!lostReal.length && !gainedReal.length) return { status: "ok", kind: "same-solutions", probed: ta };
    if (lostReal.length && !gainedReal.length) return { status: "wrong", kind: "lost-solutions", lost: lostReal, message: `This step loses the solution ${x} = ${fmt(lostReal[0])}.` };
    if (!lostReal.length && gainedReal.length) {
      return { status: "ok-conditional", kind: "gained-solutions", gained: gainedReal,
        message: `This step can add a solution that the previous line does not have (${x} = ${fmt(gainedReal[0])}). That is allowed (for example after squaring both sides), but every candidate must be checked in the original equation.` };
    }
    return { status: "wrong", kind: "different-solutions", lost: lostReal, gained: gainedReal, message: `The solutions change: ${x} = ${fmt(lostReal[0])} works before this step but not after.` };
  }
  // inequalities / mixed: compare truth at many points
  const pts = [];
  for (let i = 0; i <= 400; i++) pts.push(-50 + i * 0.25 + 0.0173);
  const special = [...(a.k === "rel" || a.k === "eq" ? probeRoots(residual(a), x) : []), ...(b.k === "rel" || b.k === "eq" ? probeRoots(residual(b), x) : [])];
  for (const s of special) pts.push(s - 1e-4, s + 1e-4, s);
  for (const p of pts) {
    const ta = truth(a, { [x]: p }, "real", 1e-9), tb = truth(b, { [x]: p }, "real", 1e-9);
    if (ta === null && tb === null) continue;
    if (ta !== tb) {
      if (ta === true && tb !== true) return { status: "wrong", kind: "lost-solutions", counterexample: { [x]: p }, message: `${x} = ${fmt(p)} satisfies the previous line but not this one.${flipHint(a, b)}` };
      if (tb === true && ta !== true) {
        return { status: "wrong", kind: "gained-solutions", counterexample: { [x]: p }, message: `${x} = ${fmt(p)} satisfies this line but not the previous one.${flipHint(a, b)}` };
      }
    }
  }
  return { status: "ok", kind: "same-solutions" };
}
function compareMultivar(a, b, vars) {
  if (a.k === "eq" && b.k === "eq") {
    const ratio = simplify(X.div(residual(a), residual(b)));
    if (X.isNum(ratio) && !X.isZero(ratio)) return { status: "ok", kind: "same-solutions" };
    // solved-for form: if b is v = expr, substitute into a
    for (const side of [0, 1]) {
      const v = b.args[side], e = b.args[1 - side];
      if (v.k === "sym" && X.freeOf(e, v)) {
        const back = simplify(X.subs(residual(a), new Map([[v.name, e]])));
        if (back === X.ZERO) return { status: "ok", kind: "solved-for", message: `Solved for ${v.name}.` };
        const r = equivalent(back, X.ZERO);
        if (r.status.startsWith("equivalent")) return { status: "ok", kind: "solved-for" };
        return { status: "wrong", kind: "different-solutions", message: `Substituting ${v.name} = ${toText(e)} back into the previous line does not satisfy it.` };
      }
    }
  }
  return { status: "unchecked", kind: "multivariable", message: "Relations in several variables are only checked when one line solves for a variable or the lines are multiples of each other." };
}
function flipHint(a, b) {
  if (a.k === "rel" && b.k === "rel" && a.op !== b.op) return "";
  if (a.k === "rel" && b.k === "rel" && a.op === b.op) return " If you multiplied or divided by a negative number, the inequality sign must flip.";
  return "";
}
const fmt = (t) => String(+t.toPrecision(8));

// ---------- mistake catalogue ----------
// Each entry rewrites the PREVIOUS line the wrong way; if that reproduces the student's line,
// we report the named misconception.
const CATALOGUE = [
  { id: "square-of-sum", name: "Squared a sum term by term", explain: "(a + b)^2 is a^2 + 2ab + b^2, not a^2 + b^2. The middle term 2ab is missing.",
    rewrite: (u) => X.mapTree(u, (w) => (w.k === "pow" && w.args[0].k === "add" && X.isInt(w.args[1]) && w.args[1].v.n > 1n ? X.add(...w.args[0].args.map((t) => X.pow(t, w.args[1]))) : w)) },
  { id: "root-of-sum", name: "Took a root term by term", explain: "sqrt(a + b) is not sqrt(a) + sqrt(b). Roots do not distribute over addition.",
    rewrite: (u) => X.mapTree(u, (w) => (w.k === "pow" && w.args[0].k === "add" && X.isNum(w.args[1]) && w.args[1].v.d !== 1n ? X.add(...w.args[0].args.map((t) => naivePow(t, w.args[1]))) : w)) },
  { id: "log-of-sum", name: "Split a logarithm of a sum", explain: "ln(a + b) is not ln(a) + ln(b). The product rule is ln(ab) = ln(a) + ln(b).",
    rewrite: (u) => X.mapTree(u, (w) => (w.k === "fn" && (w.name === "ln" || w.name === "log") && w.args[w.args.length - 1].k === "add" ? X.add(...w.args[w.args.length - 1].args.map((t) => X.fn(w.name, ...w.args.slice(0, -1), t))) : w)) },
  { id: "sign-distribute", name: "Sign error when removing brackets", explain: "A minus sign in front of brackets changes the sign of every term inside: -(a - b) = -a + b.",
    rewrite: (u) => X.mapTree(u, (w) => {
      if (w.k !== "mul" || !w.args.some((f) => X.isNum(f) && f.v.n < 0n)) return w;
      const i = w.args.findIndex((f) => f.k === "add");
      if (i < 0) return w;
      const others = w.args.filter((_, j) => j !== i);
      const [first, ...rest] = w.args[i].args;
      return X.add(X.mul(...others, first), ...rest);
    }) },
  { id: "distribute-first-only", name: "Distributed to the first term only", explain: "A factor in front of brackets multiplies every term inside: a(b + c) = ab + ac.",
    rewrite: (u) => X.mapTree(u, (w) => {
      if (w.k !== "mul" || w.args.some((f) => X.isNum(f) && f.v.n < 0n)) return w;
      const i = w.args.findIndex((f) => f.k === "add");
      if (i < 0) return w;
      const others = w.args.filter((_, j) => j !== i);
      const [first, ...rest] = w.args[i].args;
      return X.add(X.mul(...others, first), ...rest);
    }) },
  { id: "power-of-product-add", name: "Added exponents that should multiply", explain: "(a^m)^n = a^(m*n). Exponents are added only when multiplying powers of the same base: a^m * a^n = a^(m+n).",
    rewrite: (u) => X.mapTree(u, (w) => (w.k === "pow" && w.args[0].k === "pow" ? X.pow(w.args[0].args[0], X.add(w.args[0].args[1], w.args[1])) : w)) },
  { id: "cancel-terms", name: "Cancelled terms instead of factors", explain: "Only common factors cancel in a fraction. (a + b)/a is not b; it equals 1 + b/a.",
    rewrite: (u) => X.mapTree(u, (w) => {
      if (w.k !== "mul") return w;
      const den = w.args.find((f) => f.k === "pow" && X.isNum(f.args[1]) && f.args[1].v.n < 0n);
      const num = w.args.find((f) => f.k === "add");
      if (!den || !num) return w;
      const d = den.args[0];
      const kept = num.args.filter((t) => t !== d);
      if (kept.length === num.args.length) return w;
      return X.add(...kept);
    }) },
];

// (x^2)^(1/2) -> x : the classic "roots cancel powers" slip (ignores |x|)
function naivePow(t, e) {
  if (X.isNum(t) && t.v.n >= 0n) return X.pow(t, e);
  if (t.k === "pow" && X.isNum(t.args[1])) return X.pow(t.args[0], X.num(N.mul(t.args[1].v, e.v)));
  return X.pow(t, e);
}

// moving a term across the equals sign without changing its sign
function moveWithoutSignChange(prev) {
  if (prev.k !== "eq" && prev.k !== "rel") return [];
  const [l, r] = prev.args;
  const out = [];
  const lt = l.k === "add" ? l.args : [l];
  lt.forEach((t, i) => {
    if (lt.length < 2) return;
    const rest = lt.filter((_, j) => j !== i);
    out.push(X.withArgs(prev, [X.add(...rest), X.add(r, t)]));
  });
  return out;
}
// dividing every term by a coefficient except one
function divideOneTerm(prev) {
  if (prev.k !== "eq") return [];
  const [l, r] = prev.args;
  const lt = l.k === "add" ? l.args : [l], rt = r.k === "add" ? r.args : [r];
  const out = [];
  const coeffs = new Set();
  for (const t of [...lt, ...rt]) { const [q] = X.coeffAndTerm(t); const c = X.num(q); if (c !== X.ONE && c !== X.NEG_ONE && !X.isZero(c)) coeffs.add(c); }
  for (const c of coeffs) {
    const all = [...lt.map((t, i) => ["l", i]), ...rt.map((t, i) => ["r", i])];
    for (const [side, skip] of all) {
      const dl = lt.map((t, i) => (side === "l" && i === skip ? t : X.div(t, c)));
      const dr = rt.map((t, i) => (side === "r" && i === skip ? t : X.div(t, c)));
      out.push(X.eq(X.add(...dl), X.add(...dr)));
    }
  }
  return out;
}

export function diagnose(prev, cur) {
  const found = [];
  const same = (cand) => {
    try {
      const a = simplify(cand), b = cur;
      if (isRelation(a) && isRelation(b)) {
        const ra = residual(a), rb = residual(b);
        if (!ra || !rb) return false;
        const ratio = simplify(X.div(ra, rb));
        return X.isNum(ratio) && !X.isZero(ratio) || equivalent(ra, rb).status.startsWith("equivalent");
      }
      return equivalent(a, b).status.startsWith("equivalent");
    } catch (_) { return false; }
  };
  const raw = prev.raw || prev.node;
  for (const m of CATALOGUE) {
    const cand = m.rewrite(raw);
    if (cand !== raw && same(cand)) found.push({ id: m.id, name: m.name, explain: m.explain });
  }
  for (const cand of moveWithoutSignChange(raw)) if (same(cand)) { found.push({ id: "move-no-sign-change", name: "Moved a term without changing its sign", explain: "When a term moves to the other side of an equation it changes sign: a + b = c becomes a = c - b." }); break; }
  for (const cand of divideOneTerm(raw)) if (same(cand)) { found.push({ id: "divide-one-term", name: "Divided only part of a side", explain: "Dividing an equation means dividing every term on both sides by the same number." }); break; }
  if (raw.k === "rel" && cur.k === "rel" && raw.op === cur.op) {
    // multiplied by a negative without flipping?
    const flipped = X.rel(flipOp(cur.op), cur.args[0], cur.args[1]);
    if (compareRelations(raw.k === "rel" ? simplify(raw) : raw, flipped, [...X.freeSymbols(raw)]).status === "ok")
      found.push({ id: "no-flip", name: "Did not flip the inequality", explain: "Multiplying or dividing both sides of an inequality by a negative number reverses its direction." });
  }
  return found;
}
const flipOp = (op) => ({ "<": ">", ">": "<", "<=": ">=", ">=": "<=" })[op] || op;

// Check a list of lines (strings). The first line is the problem; each following line should be
// equivalent to the one before (or a valid conclusion such as "x = 2").
export function checkLines(lines, opts = {}) {
  const parsed = [];
  for (let i = 0; i < lines.length; i++) {
    const src = String(lines[i]).trim();
    if (!src) continue;
    try {
      const { node, warnings } = parseDetailed(src);
      parsed.push({ line: i + 1, src, raw: node, node: simplify(node), warnings });
    } catch (e) {
      parsed.push({ line: i + 1, src, error: e.message, pos: e.pos, hint: e.hint });
    }
  }
  const transitions = [];
  for (let i = 1; i < parsed.length; i++) {
    const a = parsed[i - 1], b = parsed[i];
    if (a.error || b.error) { transitions.push({ from: a.line, to: b.line, status: "unchecked", kind: "parse-error", message: `Line ${(b.error ? b : a).line} could not be read: ${(b.error ? b : a).error}` }); continue; }
    transitions.push({ from: a.line, to: b.line, ...judge(a, b, opts) });
  }
  const firstWrong = transitions.find((t) => t.status === "wrong");
  return {
    lines: parsed.map((p) => ({ line: p.line, src: p.src, text: p.node ? toText(p.node) : null, error: p.error || null, warnings: p.warnings || [] })),
    transitions,
    verdict: firstWrong ? "mistake" : transitions.some((t) => t.status === "unchecked") ? "partly-checked" : "all-correct",
    firstMistake: firstWrong || null,
  };
}

function judge(a, b, opts) {
  const A = a.node, B = b.node;
  const relA = isRelation(A), relB = isRelation(B);
  if (relA !== relB) {
    if (relA && !relB) return { status: "unchecked", kind: "shape-change", message: "An equation turned into an expression; keep both sides." };
    return { status: "unchecked", kind: "shape-change", message: "An expression turned into an equation." };
  }
  let res;
  if (!relA) {
    const r = equivalent(A, B);
    if (r.status.startsWith("equivalent")) res = { status: "ok", kind: "equal-expressions" };
    else if (r.status === "different") res = { status: "wrong", kind: "not-equal", counterexample: r.counterexample,
      message: `These are not equal: at ${Object.entries(r.counterexample).map(([k, v]) => `${k} = ${fmt(v)}`).join(", ")} the previous line is ${fmt(r.values[0].re)} but this line is ${fmt(r.values[1].re)}.` };
    else res = { status: "unchecked", kind: "inconclusive", message: "Could not decide whether these are equal." };
  } else {
    const vars = [...new Set([...X.freeSymbols(A), ...X.freeSymbols(B)])];
    res = compareRelations(A, B, vars);
  }
  if (res.status === "wrong") {
    const d = diagnose(a, B);
    if (d.length) res.diagnosis = d;
  }
  return res;
}
