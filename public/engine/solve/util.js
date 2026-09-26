// Quelvra solvers: shared helpers.
//
// Every solver in engine/solve/ follows one discipline:
//   1. transform the equation with steps that are EQUIVALENCES or IMPLICATIONS (never lose a root);
//   2. produce a candidate set that provably contains every solution;
//   3. check every candidate against the ORIGINAL problem (exact substitution first, then
//      multiprecision evaluation) and list the rejected ones with the reason;
//   4. hand the orchestrator a verify() that re-checks the answers with verify.js, independently.
// Nothing here uses a fresh global simplifier budget: every call gets its own context.

import * as X from "../expr.js";
import * as Q from "../num.js";
import { simplify, expand, together, numerDenom, makeCtx } from "../simplify.js";
import { toText } from "../print.js";
import { N as numN } from "../numeric.js";
import { evalC, definedAt, verifySolution, isRealC } from "../verify.js";

export { X, Q, toText };

// ---------------------------------------------------------------- canonical helpers
const OPS = 400000;
export const ctx0 = (domain = "real") => makeCtx({ domain, budget: { ops: OPS } });
export function C(u, domain = "real") { return simplify(u, ctx0(domain)); }
export function EX(u, domain = "real") { return expand(u, ctx0(domain)); }
export function TOG(u, domain = "real") { return together(u, ctx0(domain)); }
export function safe(fn, dflt = null) {
  try { return fn(); } catch (e) { if (e && (e.code === "TIMEOUT")) throw e; return dflt; }
}
// numerator / denominator of an expression after bringing it over a common denominator
export function numDen(u, domain = "real") {
  const t = TOG(C(u, domain), domain);
  const [n, d] = numerDenom(t);
  return [C(n, domain), C(d, domain)];
}
export const num = (n, d = 1n) => X.num(Q.Q(BigInt(n), BigInt(d)));
export const rat = (r) => X.num(r);
export const isConstTree = (u) => X.freeSymbols(u).size === 0;
export const sameTree = (a, b) => a === b;
export function difference(eqNode, domain) {
  if (eqNode.k === "eq" || eqNode.k === "rel") return C(X.sub(eqNode.args[0], eqNode.args[1]), domain);
  return C(eqNode, domain);
}

// ln(n) for a positive rational n -> sum of multiples of ln(prime): lets ln(4)/ln(2) cancel.
function lnSplit(r) {
  const parts = [];
  const add = (n, sgn) => {
    if (n === 1n) return true;
    const { factors, rest } = Q.trialFactor(n);
    if (rest !== 1n) return false;
    for (const [p, e] of factors) parts.push(X.mul(X.num(Q.Q(sgn * BigInt(e))), X.fn("ln", X.num(Q.Q(p)))));
    return true;
  };
  if (r.n <= 0n) return null;
  if (r.n > 10n ** 12n || r.d > 10n ** 12n) return null;
  if (!add(r.n, 1n) || !add(r.d, -1n)) return null;
  return X.add(...parts);
}
// Tidy an exact result: canonical form, with logarithms of integers split into primes when
// that makes the tree smaller (ln(4)/ln(2) -> 2), and log(b, u) of numbers evaluated.
export function tidy(u, domain = "real") {
  let s;
  try { s = C(u, domain); } catch (e) { if (e.code === "TIMEOUT") throw e; return u; }
  if (!X.contains(s, X.E) && !hasFn(s, "ln") && !hasFn(s, "log")) return s;
  try {
    const t = X.mapTree(s, (w) => {
      if (w.k === "fn" && w.name === "ln" && X.isNum(w.args[0])) { const sp = lnSplit(w.args[0].v); return sp || w; }
      if (w.k === "fn" && w.name === "log" && w.args.length === 2 && X.isNum(w.args[0]) && X.isNum(w.args[1])) {
        const a = lnSplit(w.args[1].v), b = lnSplit(w.args[0].v);
        if (a && b) return X.div(a, b);
      }
      return w;
    });
    if (t === s) return s;
    const r = C(t, domain);
    const r2 = safe(() => C(TOG(r, domain), domain), r);
    const best = [r, r2].reduce((m, v) => (v && X.size(v) < X.size(m) ? v : m), s);
    return best;
  } catch (e) { if (e.code === "TIMEOUT") throw e; return s; }
}
export function hasFn(u, name) {
  if (u.k === "fn" && (!name || u.name === name)) return true;
  return u.args.some((a) => hasFn(a, name));
}
export function findAll(u, pred, out = []) {
  if (pred(u)) { if (!out.includes(u)) out.push(u); return out; }
  for (const a of u.args) findAll(a, pred, out);
  return out;
}
export function findAllDeep(u, pred, out = []) {
  if (pred(u) && !out.includes(u)) out.push(u);
  for (const a of u.args) findAllDeep(a, pred, out);
  return out;
}

// ---------------------------------------------------------------- numbers
export const cval = (u, mode = "complex") => evalC(u, {}, mode);
export function fval(u) { const c = evalC(u, {}, "real"); return Number.isFinite(c.re) && isRealC(c, 1e-9) ? c.re : NaN; }
// Multiprecision value of a constant tree: { re, im, err, ok, undefined }.
export function hp(u, digits = 30) {
  let r;
  try { r = numN(u, digits, { timeLimitMs: 1500 }); } catch (e) { if (e && e.code === "TIMEOUT") throw e; return { ok: false }; }
  if (!r || r.value === "undefined") return { ok: false, undefined: true };
  if (!r.value) return { ok: false };
  let re = 0, im = 0;
  const v = r.value.trim();
  if (v.endsWith("i")) {
    const cut = Math.max(v.lastIndexOf(" + "), v.lastIndexOf(" - "));
    const imPart = cut >= 0 ? v.slice(cut + 1).replace(/\s+/g, "") : v;
    if (cut >= 0) re = parseFloat(v.slice(0, cut));
    const s = imPart.slice(0, -1);
    im = s === "" || s === "+" ? 1 : s === "-" ? -1 : parseFloat(s);
  } else re = parseFloat(v);
  if (!Number.isFinite(re) || !Number.isFinite(im)) return { ok: false };
  const err = r.errorBound == null ? Infinity : parseFloat(r.errorBound);
  return { ok: true, re, im, err, rec: r, zero: r.value === "0", converged: r.converged };
}
// Sign of a real constant: 1, -1, 0 (proven exactly), or null (undecided).
export function signConst(u, domain = "real") {
  let s;
  try { s = C(u, domain); } catch (e) { if (e.code === "TIMEOUT") throw e; s = u; }
  if (s === X.UNDEF) return null;
  if (X.isNum(s)) return Q.sign(s.v);
  const h = hp(s, 30);
  if (h.ok && Math.abs(h.im) > (h.err || 0) * 4 && Math.abs(h.im) > 1e-25) return null; // not real
  if (h.ok && !h.zero && Math.abs(h.re) > 4 * h.err && Number.isFinite(h.re)) return h.re > 0 ? 1 : -1;
  if (isZeroExact(s, domain)) return 0;
  const h2 = hp(s, 60);
  if (h2.ok && !h2.zero && Math.abs(h2.re) > 4 * h2.err) return h2.re > 0 ? 1 : -1;
  return null;
}
// Is a constant tree exactly zero? (proof by canonicalisation, expansion or rationalisation)
export function isZeroExact(u, domain = "real") {
  try {
    const s = C(u, domain);
    if (s === X.ZERO) return true;
    if (X.isNum(s)) return false;
    const e = EX(s, domain);
    if (e === X.ZERO) return true;
    const [n] = numDen(e, domain);
    if (n === X.ZERO) return true;
    const e2 = EX(n, domain);
    if (e2 === X.ZERO) return true;
  } catch (e) { if (e.code === "TIMEOUT") throw e; }
  return false;
}
// Numerically zero at high precision (evidence, not proof).
export function nearZero(u, digits = 40) {
  const h = hp(u, digits);
  if (!h.ok) return false;
  if (h.zero) return true;
  const mag = Math.hypot(h.re, h.im);
  return mag <= Math.max(h.err * 4, 10 ** -(digits - 8));
}
// Compare two real constants: -1, 0, 1 or null.
export function cmpConst(a, b, domain = "real") {
  if (a === b) return 0;
  return signConst(X.sub(a, b), domain);
}
// Approx record for a constant tree at `digits` significant digits.
export function approxRec(u, digits = 20) {
  try {
    const r = numN(u, digits, { timeLimitMs: 2000 });
    if (!r || r.value === "undefined" || !r.value) return null;
    return r;
  } catch (e) { if (e && e.code === "TIMEOUT") throw e; return null; }
}

// Rational approximation (continued fractions) with bounded denominator.
export function ratApprox(x, maxDen = 1000) {
  if (!Number.isFinite(x) || Math.abs(x) > 1e12) return null;
  let h0 = 1, h1 = Math.floor(x), k0 = 0, k1 = 1, f = x - Math.floor(x);
  for (let i = 0; i < 30 && f > 1e-15; i++) {
    const a = Math.floor(1 / f);
    const h2 = a * h1 + h0, k2 = a * k1 + k0;
    if (k2 > maxDen) break;
    h0 = h1; h1 = h2; k0 = k1; k1 = k2;
    f = 1 / f - a;
  }
  return Q.Q(BigInt(Math.round(h1)), BigInt(k1));
}
// A simple rational strictly between a < b (numbers).
export function rationalBetween(a, b) {
  if (!(a < b)) return null;
  if (!Number.isFinite(a) && !Number.isFinite(b)) return Q.Q(0n);
  if (!Number.isFinite(a)) { const f = Math.floor(b) - 1; return Q.Q(BigInt(Math.min(f, 0 < b ? 0 : f))); }
  if (!Number.isFinite(b)) { const c = Math.ceil(a) + 1; return Q.Q(BigInt(Math.max(c, 0 > a ? 0 : c))); }
  if (a < 0 && b > 0) return Q.Q(0n);
  // smallest-denominator rational in (a, b) by Stern-Brocot style search on denominators
  for (let d = 1; d <= 1 << 20; d *= 2) {
    const n = Math.floor(a * d) + 1;
    if (n / d < b && n / d > a) {
      // try integers first
      const i = Math.ceil(a + 1e-300);
      if (i > a && i < b && Number.isSafeInteger(i)) return Q.Q(BigInt(i));
      return Q.Q(BigInt(n), BigInt(d));
    }
  }
  const m = (a + b) / 2;
  return Q.fromDecimal ? Q.fromDecimal(m.toPrecision(17)) : Q.Q(BigInt(Math.round(m * 1e9)), 1000000000n);
}

// ---------------------------------------------------------------- checking candidates
// Denominators appearing in a tree (bases raised to negative powers, tan/sec/... arguments).
export function denominators(u) {
  const out = [];
  const walk = (w) => {
    if (w.k === "pow" && X.isNum(w.args[1]) && Q.isNeg(w.args[1].v)) { if (!out.includes(w.args[0])) out.push(w.args[0]); }
    for (const a of w.args) walk(a);
  };
  walk(u);
  return out;
}

// Check one candidate value r (tree) for unknown x against the ORIGINAL relation.
// Returns { ok: true, level: "exact"|"numeric" } or { ok: false, reason }.
export function checkCandidate(original, x, r, domain = "real", extraVars = null) {
  const xn = typeof x === "string" ? x : x.name;
  const env = new Map([[xn, r]]);
  if (extraVars) for (const [k, v] of extraVars) env.set(k, v);
  // numeric domain check first
  const numEnv = {};
  for (const [k, v] of env) numEnv[k] = evalC(v, {}, "complex");
  for (const [k, c] of Object.entries(numEnv)) {
    if (!Number.isFinite(c.re) || !Number.isFinite(c.im)) {
      // may still be fine exactly (huge numbers); fall back to exact substitution below
      numEnv[k] = null;
    } else if (domain === "real" && !isRealC(c, 1e-10)) {
      const h = hp(env.get(k), 30);
      if (!(h.ok && Math.abs(h.im) <= Math.max(1e-25, 4 * h.err))) return { ok: false, reason: `${k} = ${toText(env.get(k))} is not a real number` };
      numEnv[k] = { re: c.re, im: 0 };
    }
  }
  const rels = original.k === "system" || original.k === "and" ? original.args : [original];
  // exact denominator check on the ORIGINAL problem
  for (const d of denominators(original)) {
    const v = safe(() => C(X.subs(d, env), domain));
    if (v === X.ZERO) return { ok: false, reason: `it makes the denominator ${toText(d)} of the original equation zero` };
  }
  if (Object.values(numEnv).every((v) => v) && !definedAt(original, numEnv, domain === "real" ? "real" : "complex")) {
    // confirm with multiprecision evaluation of every relation side (double precision can misjudge)
    let undefinedConfirmed = false;
    for (const rel of rels) for (const side of rel.args) {
      const v = safe(() => X.subs(side, env));
      if (!v) continue;
      const h = hp(v, 30);
      if (!h.ok) { undefinedConfirmed = true; break; }
      if (domain === "real" && Math.abs(h.im) > Math.max(1e-25, 4 * h.err)) { undefinedConfirmed = true; break; }
    }
    if (undefinedConfirmed) return { ok: false, reason: "the original equation is undefined there (outside its domain)" };
  }
  let level = "exact";
  for (const rel of rels) {
    if (rel.k === "bool") { if (rel === X.TRUE) continue; return { ok: false, reason: "false" }; }
    if (rel.k === "fn") continue;
    const L = X.subs(rel.args[0], env), R = X.subs(rel.args[1], env);
    const d = X.sub(L, R);
    if (rel.k === "eq") {
      // domain of the substituted sides in multiprecision (catches sqrt of negatives exactly)
      for (const side of [L, R]) {
        const h = hp(side, 30);
        if (h.undefined) return { ok: false, reason: "the original equation is undefined there" };
        if (h.ok && domain === "real" && Math.abs(h.im) > Math.max(1e-25, 8 * h.err) && Math.abs(h.im) > 1e-20 * Math.max(1, Math.abs(h.re))) return { ok: false, reason: "a side of the original equation is not real there" };
      }
      if (isZeroExact(d, domain)) continue;
      const h = hp(d, 40);
      if (h.ok && !h.zero && Math.hypot(h.re, h.im) > Math.max(8 * h.err, 1e-30)) {
        return { ok: false, reason: `substituting gives ${fmtNum(h)} instead of 0 (extraneous)` };
      }
      if (nearZero(d, 40) && nearZero(d, 80)) { level = "numeric"; continue; }
      return { ok: false, reason: "could not confirm that it satisfies the original equation" };
    }
    // inequality relation
    const s = signConst(d, domain);
    if (s === null) return { ok: false, reason: "could not decide the inequality there" };
    const op = rel.op;
    const good = op === "<" ? s < 0 : op === "<=" ? s <= 0 : op === ">" ? s > 0 : op === ">=" ? s >= 0 : op === "!=" ? s !== 0 : false;
    if (!good) return { ok: false, reason: "the inequality does not hold there" };
  }
  return { ok: true, level };
}
function fmtNum(h) { const v = h.im ? `${+h.re.toPrecision(8)} + ${+h.im.toPrecision(8)}i` : `${+h.re.toPrecision(8)}`; return v; }

// Deduplicate exact trees by value (exact difference zero, or equal at 40 digits).
export function dedupeTrees(list, domain = "real") {
  const out = [];
  for (const it of list) {
    const t = it.tree || it;
    const v = cval(t);
    let dup = -1;
    for (let i = 0; i < out.length; i++) {
      const o = out[i].tree || out[i];
      if (o === t) { dup = i; break; }
      const w = cval(o);
      if (Number.isFinite(v.re) && Number.isFinite(w.re) && Math.hypot(v.re - w.re, v.im - w.im) > 1e-8 * Math.max(1, Math.hypot(v.re, v.im))) continue;
      if (isZeroExact(X.sub(t, o), domain) || nearZero(X.sub(t, o), 50)) { dup = i; break; }
    }
    if (dup < 0) out.push(it);
    else if (it.multiplicity && out[dup].multiplicity) out[dup] = { ...out[dup], multiplicity: Math.max(out[dup].multiplicity, it.multiplicity) };
  }
  return out;
}

// ---------------------------------------------------------------- verification helpers
export function toStatus(r) { return r; }
// verify.js on every exact / approximate root against the ORIGINAL equation.
export function verifyRootsWithVerifyJs(original, x, answers, domain) {
  const results = [];
  for (const a of answers) {
    let tree = a.tree;
    if (a.kind === "approx" || (a.tree && hasFn(a.tree, "W"))) {
      const v = a.approx ? a.approx.value : null;
      if (!v) { results.push({ status: "inconclusive", checks: [{ kind: "substitution", ok: null, detail: "no value to substitute" }] }); continue; }
      tree = decimalTree(v);
      if (!tree) { results.push({ status: "inconclusive", checks: [{ kind: "substitution", ok: null, detail: "value not parseable" }] }); continue; }
      const r = verifySolution(original, new Map([[x, tree]]), { domain });
      // an approximate root satisfies the equation only approximately: the verifier's
      // numeric tolerance (1e-9 relative) is what certifies it
      results.push(r.status === "verified-exact" ? { ...r, status: "verified-numeric" } : r);
      continue;
    }
    if (!tree) continue;
    results.push(verifySolution(original, new Map([[x, tree]]), { domain }));
  }
  return results;
}
export function decimalTree(s) {
  const t = String(s).trim();
  if (!/^-?\d+(\.\d+)?(e[+-]?\d+)?$/i.test(t)) return null;
  try {
    const m = /^(-?)(\d+)(?:\.(\d+))?(?:e([+-]?\d+))?$/i.exec(t);
    let n = BigInt(m[2] + (m[3] || "")), d = 10n ** BigInt((m[3] || "").length);
    const e = m[4] ? parseInt(m[4], 10) : 0;
    if (e > 0) n *= 10n ** BigInt(e); else if (e < 0) d *= 10n ** BigInt(-e);
    if (m[1]) n = -n;
    return X.num(Q.Q(n, d));
  } catch (_) { return null; }
}
export const passCheck = (kind, detail, method = "exact") => ({ status: method === "numeric" ? "verified-numeric" : "verified-exact", checks: [{ kind, ok: true, detail }] });
export const failCheck = (kind, detail) => ({ status: "failed", checks: [{ kind, ok: false, detail }] });
export const openCheck = (kind, detail) => ({ status: "inconclusive", checks: [{ kind, ok: null, detail }] });

// ---------------------------------------------------------------- answers
export function exactAnswer(x, tree, digits, extra = {}) {
  const a = { kind: "exact", label: x, tree, ...extra };
  if (!X.isNum(tree) || tree.v.d !== 1n) {
    if (isConstTree(tree)) {
      const ap = hasFn(tree, "W") ? extra.approx || null : approxRec(tree, digits);
      if (ap) a.approx = ap;
    }
  }
  return a;
}
export function numericValueOf(a) {
  if (a.tree && isConstTree(a.tree) && !hasFn(a.tree, "W")) { const c = cval(a.tree); return c; }
  if (a.approx && a.approx.value) { const v = parseFloat(a.approx.value); return { re: v, im: 0 }; }
  return null;
}
// Build a compare(other) closure for cross-checking one candidate against another.
// sig: { reals: [numbers], complete, window: [lo, hi] | null, general: [{offset, period}] }
export function makeCompare(sig) {
  return (other) => {
    const os = other && other.signature;
    if (!os) return true;
    return signaturesAgree(sig, os);
  };
}
export function signaturesAgree(a, b) {
  if (a.kind !== b.kind) {
    // general (periodic) families vs a numeric list of roots in a window
    if (a.kind === "general" && b.kind === "roots") return rootsInFamilies(b.reals, a.general, b.window) && familyMembersFound(a.general, b.reals, b.window, b.complete);
    if (b.kind === "general" && a.kind === "roots") return rootsInFamilies(a.reals, b.general, a.window) && familyMembersFound(b.general, a.reals, a.window, a.complete);
    return true;
  }
  if (a.kind === "roots") {
    const lo = Math.max(a.window ? a.window[0] : -Infinity, b.window ? b.window[0] : -Infinity);
    const hi = Math.min(a.window ? a.window[1] : Infinity, b.window ? b.window[1] : Infinity);
    const A = a.reals.filter((v) => v >= lo && v <= hi), B = b.reals.filter((v) => v >= lo && v <= hi);
    const close = (u, v) => Math.abs(u - v) <= 1e-7 * Math.max(1, Math.abs(u));
    // an incomplete side may miss roots; it may not have extra ones
    for (const v of A) if (!B.some((w) => close(v, w)) && b.complete) return false;
    for (const v of B) if (!A.some((w) => close(v, w)) && a.complete) return false;
    return true;
  }
  if (a.kind === "set") {
    for (const t of a.probe || []) {
      if (!b.test) break;
      if (a.test(t) !== b.test(t)) return false;
    }
    return true;
  }
  if (a.kind === "tuples") {
    const close = (u, v) => u.length === v.length && u.every((z, i) => Math.hypot(z.re - v[i].re, z.im - v[i].im) <= 1e-7 * Math.max(1, Math.hypot(z.re, z.im)));
    for (const s of a.sols) if (!b.sols.some((t) => close(s, t)) && b.complete) return false;
    for (const s of b.sols) if (!a.sols.some((t) => close(s, t)) && a.complete) return false;
    return true;
  }
  return true;
}
function rootsInFamilies(reals, fams, win) {
  return reals.every((v) => fams.some((f) => { const k = Math.round((v - f.offset) / f.period); return Math.abs(f.offset + k * f.period - v) <= 1e-7 * Math.max(1, Math.abs(v)); }));
}
function familyMembersFound(fams, reals, win, complete) {
  if (!win || !complete) return true;
  for (const f of fams) {
    const k0 = Math.ceil((win[0] - f.offset) / f.period), k1 = Math.floor((win[1] - f.offset) / f.period);
    for (let k = k0; k <= k1 && k - k0 < 2000; k++) {
      const v = f.offset + k * f.period;
      if (v <= win[0] + 1e-9 || v >= win[1] - 1e-9) continue;
      if (!reals.some((w) => Math.abs(w - v) <= 1e-7 * Math.max(1, Math.abs(v)))) return false;
    }
  }
  return true;
}

// error with code (UNSUPPORTED etc.)
export function fail(message, code = "UNSUPPORTED") { const e = new Error(message); e.code = code; return e; }

// Strip a solve(...) command wrapper and report the requested variable.
export function unwrap(node) {
  if (node.k === "fn" && node.name === "solve" && node.args[0]) {
    const v = node.args.slice(1).filter((a) => a.k === "sym").map((a) => a.name);
    return { node: node.args[0], vars: v };
  }
  return { node, vars: [] };
}
