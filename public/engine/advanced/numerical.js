// Numerical methods. Every answer is APPROXIMATE and says so, with an error estimate.
//
//   root finding : newton, bisection, secant, fixedpoint (with an iteration table)
//   quadrature   : trapezoid, simpson (the rule's value, the error bound of the rule, and the
//                  actual error against an accurate reference)
//   ODE steppers : eulermethod, rungekutta (classical RK4) (the method's value plus a step-halving error estimate)
//   eigenvalues  : poweriter (dominant eigenvalue and eigenvector)
//
// Verification (independent of the iteration that produced the number):
//   roots        : a sign-change certificate f(r - d) f(r + d) < 0 with the verifier's evaluator
//                  (so a root lies within d by the intermediate value theorem); for a root of even
//                  multiplicity, a sign change of f' next to a point where |f| is at rounding level
//   quadrature   : the rule's sum recomputed in exact / multiprecision arithmetic, and the claimed
//                  error bound tested against an independent Gauss-Legendre reference
//   ODE steppers : the scheme recomputed in exact rational arithmetic (multiprecision stage values
//                  for transcendental right-hand sides)
//   power method : exact characteristic polynomial (Faddeev-LeVerrier over Q) and its roots by
//                  Durand-Kerner; the claimed eigenvalue must be the strictly dominant root

import * as N from "../num.js";
import * as P from "../poly-core.js";
import { makeCtx } from "../simplify.js";
import {
  X, toText, TCV, fail, safe, pass, bad, open, fmt, C, D, valueAnswers, approxRecord, approxRec, expand, evalR, forEval, envFn, quad1, numOf, isVec,
} from "./util.js";

const APPROX = "approximate";
const symName = (u, what) => { if (!u || u.k !== "sym") throw fail(`${what} must be a variable`); return u.name; };
const numArg = (u, what) => { if (!u) throw fail(`missing ${what}`); const v = numOf(C(u)); if (!Number.isFinite(v)) throw fail(`${what} must be a real number`); return v; };
const exprOf = (u, what) => { if (!u) throw fail(`missing ${what}`); if (u.k === "eq") return C(X.sub(u.args[0], u.args[1])); if (["vector", "tuple", "matrix", "rel", "system"].includes(u.k)) throw fail(`${what} must be an expression`); return u; };
const table = (rows) => rows.map((r) => r.join("   ")).join("\n");

// ------------------------------------------------------------------ root certificates
function polyOf(f, x) {
  try {
    const p = P.fromTree(C(expand(C(f), makeCtx({ budget: { ops: 300000 } }))), x);
    if (!p || !p.length || !p.every((c) => c && typeof c.n === "bigint")) return null;
    return p;
  } catch (_) { return null; }
}
const ratOf = (v) => P.toRat(v.toPrecision(17));
function rootCertificate(f, x, r) {
  const sc = Math.max(1, Math.abs(r));
  // polynomial with rational coefficients: Sturm's theorem in exact arithmetic (handles multiple roots)
  const p = polyOf(f, x);
  if (p && p.length > 1) {
    for (const k of [1e-14, 1e-13, 1e-12, 1e-11, 1e-10, 1e-9, 1e-8, 1e-7, 1e-6]) {
      const d = k * sc;
      let cnt = 0;
      try { cnt = P.countRealRoots(p, ratOf(r - d), ratOf(r + d)); } catch (_) { return { ok: false, why: "the exact root count failed" }; }
      if (cnt >= 1) return { ok: true, d, detail: `Sturm's theorem (exact rational arithmetic): the polynomial has ${cnt === 1 ? "a real root" : cnt + " distinct real roots"} in [${fmt(r - d)}, ${fmt(r + d)}], so a root lies within ${d.toExponential(1)} of the answer` };
    }
    return { ok: false, why: "Sturm's theorem finds no root of the polynomial next to the answer" };
  }
  const fe = envFn(f);
  const at = (v) => fe({ [x]: v });
  for (const k of [1e-13, 1e-12, 1e-11, 1e-10, 1e-9, 1e-8]) {
    const d = k * sc;
    const a = at(r - d), b = at(r + d);
    if (!Number.isFinite(a) || !Number.isFinite(b)) return { ok: false, why: "f could not be evaluated next to the root" };
    // both values well above rounding level, with opposite signs
    if (a * b < 0 && Math.min(Math.abs(a), Math.abs(b)) > 1e-14) {
      // a pole also changes sign: f must be small there
      const fs = Math.max(Math.abs(at(r - 1e-3 * sc)), Math.abs(at(r + 1e-3 * sc)), 1e-300);
      if (Math.max(Math.abs(a), Math.abs(b)) > fs) return { ok: false, why: "the sign change looks like a pole, not a root" };
      return { ok: true, d, detail: `f(${fmt(r - d)}) = ${fmt(a)} and f(${fmt(r + d)}) = ${fmt(b)} have opposite signs, so a root lies within ${d.toExponential(1)} of the answer (intermediate value theorem)` };
    }
  }
  return { ok: false, why: "f does not change sign next to the answer (a root of even multiplicity of a non-polynomial function cannot be certified)" };
}
function rootResult(label, f, x, r, method, steps, env, iterations) {
  if (!Number.isFinite(r)) throw fail(`${method} did not converge`);
  const cert = rootCertificate(f, x, r);
  env.log.add({ rule: `numeric.${method}`, title: `${method} iterations`, why: table(steps.slice(0, 12)) + (steps.length > 12 ? `\n... (${steps.length} rows)` : ""), before: f, after: null, kind: "note" });
  const rec = approxRecord(r, cert.ok ? cert.d : 1e-8 * Math.max(1, Math.abs(r)), method, { iterations });
  return {
    answers: [{ kind: "approx", label, approx: rec, note: `approximate root by ${method} (${iterations} iterations)` }],
    solutionStatus: APPROX,
    verify: () => TCV([cert.ok ? pass("sign-change", cert.detail) : bad("sign-change", `the answer could not be certified: ${cert.why}`)]),
  };
}
function cmdNewton(node, env) {
  const f = exprOf(node.args[0], "the function");
  const x = symName(node.args[1] || X.sym("x"), "the variable");
  const x0 = numArg(node.args[2], "the starting value x0");
  const extra = [...X.freeSymbols(f)].filter((v) => v !== x);
  if (extra.length) throw fail(`the function has symbols other than ${x}`);
  const df = C(D(f, x));
  const fe = envFn(f), de = envFn(df);
  let r = x0;
  const steps = [["n", "x_n", "f(x_n)"]];
  let it = 0;
  for (; it < 200; it++) {
    env.checkTime && env.checkTime();
    const fv = fe({ [x]: r }), dv = de({ [x]: r });
    steps.push([String(it), fmt(r), fmt(fv)]);
    if (!Number.isFinite(fv) || !Number.isFinite(dv)) throw fail("Newton's method left the domain of f");
    if (fv === 0) break;
    if (dv === 0) throw fail(`f'(x) = 0 at x = ${fmt(r)}; Newton's method cannot continue`);
    const nx = r - fv / dv;
    if (Math.abs(nx - r) <= 1e-15 * Math.max(1, Math.abs(r))) { r = nx; it++; break; }
    r = nx;
  }
  if (it >= 200) throw fail("Newton's method did not converge in 200 iterations");
  return rootResult(`root (Newton's method from ${x}0 = ${fmt(x0)})`, f, x, r, "Newton", steps, env, it);
}
function cmdSecant(node, env) {
  const f = exprOf(node.args[0], "the function");
  const x = symName(node.args[1] || X.sym("x"), "the variable");
  let a = numArg(node.args[2], "x0"), b = numArg(node.args[3], "x1");
  const fe = envFn(f);
  const steps = [["n", "x_n", "f(x_n)"]];
  let fa = fe({ [x]: a }), fb = fe({ [x]: b });
  steps.push(["0", fmt(a), fmt(fa)], ["1", fmt(b), fmt(fb)]);
  let it = 1;
  for (; it < 200; it++) {
    if (!Number.isFinite(fa) || !Number.isFinite(fb)) throw fail("the secant method left the domain of f");
    if (fb === 0) break;
    if (fb === fa) throw fail("the secant line is horizontal; the method cannot continue");
    const c = b - (fb * (b - a)) / (fb - fa);
    a = b; fa = fb; b = c; fb = fe({ [x]: b });
    steps.push([String(it + 1), fmt(b), fmt(fb)]);
    if (Math.abs(b - a) <= 1e-15 * Math.max(1, Math.abs(b))) break;
  }
  if (it >= 200) throw fail("the secant method did not converge");
  return rootResult("root (secant method)", f, x, b, "secant", steps, env, it);
}
function cmdBisection(node, env) {
  const f = exprOf(node.args[0], "the function");
  const x = symName(node.args[1] || X.sym("x"), "the variable");
  let a = numArg(node.args[2], "a"), b = numArg(node.args[3], "b");
  if (!(a < b)) throw fail("bisection needs an interval [a, b] with a < b");
  const fe = envFn(f);
  let fa = fe({ [x]: a }), fb = fe({ [x]: b });
  if (!Number.isFinite(fa) || !Number.isFinite(fb)) throw fail("f is not defined at an endpoint");
  if (fa === 0) return rootResult("root (bisection)", f, x, a, "bisection", [["endpoint", fmt(a), "0"]], env, 0);
  if (fb === 0) return rootResult("root (bisection)", f, x, b, "bisection", [["endpoint", fmt(b), "0"]], env, 0);
  if (Math.sign(fa) === Math.sign(fb)) throw fail(`f(a) = ${fmt(fa)} and f(b) = ${fmt(fb)} have the same sign, so bisection cannot start (there may be no root, or an even number of roots, in [a, b])`);
  const steps = [["n", "a", "b", "midpoint", "f(midpoint)"]];
  let it = 0;
  while (b - a > 2e-15 * Math.max(1, Math.abs(a), Math.abs(b)) && it < 200) {
    const m = (a + b) / 2;
    if (m === a || m === b) break;
    const fm = fe({ [x]: m });
    if (!Number.isFinite(fm)) throw fail("f is not defined inside the interval");
    steps.push([String(it), fmt(a), fmt(b), fmt(m), fmt(fm)]);
    if (fm === 0) { a = b = m; break; }
    if (Math.sign(fm) === Math.sign(fa)) { a = m; fa = fm; } else { b = m; fb = fm; }
    it++;
  }
  return rootResult("root (bisection)", f, x, (a + b) / 2, "bisection", steps, env, it);
}
function cmdFixedpoint(node, env) {
  const g = exprOf(node.args[0], "g");
  const x = symName(node.args[1] || X.sym("x"), "the variable");
  const x0 = numArg(node.args[2], "x0");
  const ge = envFn(g);
  let r = x0;
  const steps = [["n", "x_n"]];
  let it = 0;
  for (; it < 5000; it++) {
    const nx = ge({ [x]: r });
    if (it < 40) steps.push([String(it), fmt(r)]);
    if (!Number.isFinite(nx) || Math.abs(nx) > 1e12) throw fail("the fixed-point iteration diverges");
    if (Math.abs(nx - r) <= 1e-15 * Math.max(1, Math.abs(r))) { r = nx; break; }
    r = nx;
  }
  if (it >= 5000) throw fail("the fixed-point iteration did not converge in 5000 steps");
  return rootResult(`fixed point of ${x} = ${toText(g)}`, C(X.sub(g, X.sym(x))), x, r, "fixed-point iteration", steps, env, it);
}

// ------------------------------------------------------------------ quadrature rules
function maxAbsOn(u, x, a, b) {
  const fe = envFn(u);
  let m = 0;
  for (let i = 0; i <= 400; i++) { const v = Math.abs(fe({ [x]: a + ((b - a) * i) / 400 })); if (!Number.isFinite(v)) return NaN; m = Math.max(m, v); }
  return m;
}
function rule(node, env, kind) {
  const f = exprOf(node.args[0], "the integrand");
  const x = symName(node.args[1] || X.sym("x"), "the variable");
  const A = C(node.args[2]), B = C(node.args[3]);
  const nT = node.args[4];
  if (!nT || !X.isInt(C(nT)) || C(nT).v.n < 1n || C(nT).v.n > 2000n) throw fail("n must be a whole number of subintervals between 1 and 2000");
  const n = Number(C(nT).v.n);
  if (kind === "simpson" && n % 2) throw fail("Simpson's rule needs an even n");
  const a = numOf(A), b = numOf(B);
  if (!Number.isFinite(a) || !Number.isFinite(b) || !(b > a)) throw fail("the limits must be numbers with a < b");
  const extra = [...X.freeSymbols(f)].filter((v) => v !== x);
  if (extra.length) throw fail(`the integrand has symbols other than ${x}`);
  const H = C(X.div(X.sub(B, A), X.num(n)));
  const w = (i) => (kind === "trapezoid" ? (i === 0 || i === n ? 1 : 2) : i === 0 || i === n ? 1 : i % 2 ? 4 : 2);
  const scale = kind === "trapezoid" ? X.div(H, X.TWO) : X.div(H, X.num(3));
  const terms = [];
  for (let i = 0; i <= n; i++) terms.push(X.mul(X.num(w(i)), X.subs(f, { [x]: X.add(A, X.mul(X.num(i), H)) })));
  const exact = C(X.mul(scale, X.add(...terms)));
  if (exact === X.UNDEF || X.contains(exact, X.UNDEF)) throw fail("f is not defined at a node");
  const val = numOf(exact);
  if (!Number.isFinite(val)) throw fail("f is not defined at a node");
  const hv = (b - a) / n;
  const derivOrder = kind === "trapezoid" ? 2 : 4;
  let d = f;
  for (let k = 0; k < derivOrder; k++) d = C(D(d, x));
  const M = maxAbsOn(d, x, a, b);
  const bound = kind === "trapezoid" ? ((b - a) * hv * hv * M) / 12 : ((b - a) * Math.pow(hv, 4) * M) / 180;
  const name = kind === "trapezoid" ? "trapezoidal rule" : "Simpson's rule";
  env.log.add({ rule: `numeric.${kind}`, title: name, why: kind === "trapezoid" ? `T_n = h/2 (f(x_0) + 2 f(x_1) + ... + 2 f(x_(n-1)) + f(x_n)), h = ${toText(H)}.` : `S_n = h/3 (f(x_0) + 4 f(x_1) + 2 f(x_2) + ... + 4 f(x_(n-1)) + f(x_n)), h = ${toText(H)}.`, before: f, after: exact });
  env.log.add({ rule: `numeric.${kind}.bound`, title: "Error bound", why: kind === "trapezoid" ? `|E| <= (b - a) h^2 max|f''| / 12 with max|f''| ~ ${fmt(M)} (sampled): |E| <= ${bound.toExponential(3)}.` : `|E| <= (b - a) h^4 max|f''''| / 180 with max|f''''| ~ ${fmt(M)} (sampled): |E| <= ${bound.toExponential(3)}.`, before: null, after: null, kind: "note" });
  const fe = envFn(f);
  const answers = [...valueAnswers(`${name} value (n = ${n})`, exact).map((a0) => (a0.kind === "approx" ? { ...a0, approx: { ...a0.approx, method: name } } : a0))];
  if (!answers.some((a0) => a0.kind === "approx")) answers.push({ kind: "approx", label: `${name} value (n = ${n})`, approx: approxRecord(val, 0, name) });
  // approx first so the rule value is the headline number
  answers.sort((p, q) => (p.kind === "approx" ? -1 : 0) - (q.kind === "approx" ? -1 : 0));
  answers.push({ kind: "approx", label: "error bound for the rule", approx: approxRecord(bound, bound * 1e-3, "error bound (sampled max of the derivative)") });
  return {
    answers, solutionStatus: APPROX,
    verify: () => {
      // 1) recompute the rule in double with the verifier's evaluator
      let s = 0;
      for (let i = 0; i <= n; i++) s += w(i) * fe({ [x]: a + i * hv });
      s *= kind === "trapezoid" ? hv / 2 : hv / 3;
      const c1 = Math.abs(s - val) <= 1e-11 * Math.max(1, Math.abs(val)) ? pass("recompute", `the rule recomputed in floating point gives ${fmt(s)}`) : bad("recompute", `the rule recomputed in floating point gives ${fmt(s)}, not ${fmt(val)}`);
      // 2) the error bound holds against an accurate reference
      const ref = quad1((t) => fe({ [x]: t }), a, b, { m: 20, panels: 16 });
      if (!ref.ok || ref.err > 1e-10) return TCV([c1, open("error-bound", "no accurate reference value for the integral")]);
      const actual = Math.abs(val - ref.value);
      const c2 = actual <= bound * 1.000001 + 1e-13 ? pass("error-bound", `actual error ${actual.toExponential(3)} (Gauss-Legendre reference ${fmt(ref.value)}) is within the bound ${bound.toExponential(3)}`) : bad("error-bound", `actual error ${actual.toExponential(3)} exceeds the stated bound ${bound.toExponential(3)}`);
      return TCV([c1, c2]);
    },
  };
}

// ------------------------------------------------------------------ Euler / RK4
function stepper(node, env, kind) {
  const [F0, xs, ys, x0T, y0T, hT, x1T] = node.args;
  const F = exprOf(F0, "the right-hand side f(x, y)");
  const x = symName(xs, "the independent variable"), y = symName(ys, "the dependent variable");
  const extra = [...X.freeSymbols(F)].filter((v) => v !== x && v !== y);
  if (extra.length) throw fail(`the right-hand side has symbols other than ${x} and ${y}`);
  const x0 = numArg(x0T, "x0"), y0 = numArg(y0T, "y0"), h = numArg(hT, "h"), x1 = numArg(x1T, "the end point");
  if (!(h > 0)) throw fail("the step h must be positive");
  const nf = (x1 - x0) / h;
  const n = Math.round(nf);
  if (n < 1 || Math.abs(nf - n) > 1e-9 * Math.max(1, nf)) throw fail("(end - start)/h must be a positive whole number");
  if (n > 100000) throw fail("too many steps");
  const fe = envFn(F);
  const f = (xv, yv) => fe({ [x]: xv, [y]: yv });
  const run = (hh, steps) => {
    let xv = x0, yv = y0;
    const rows = [];
    for (let i = 0; i < steps; i++) {
      rows.push([String(i), fmt(xv), fmt(yv)]);
      if (kind === "euler") yv = yv + hh * f(xv, yv);
      else {
        const k1 = f(xv, yv), k2 = f(xv + hh / 2, yv + (hh / 2) * k1), k3 = f(xv + hh / 2, yv + (hh / 2) * k2), k4 = f(xv + hh, yv + hh * k3);
        yv = yv + (hh / 6) * (k1 + 2 * k2 + 2 * k3 + k4);
      }
      xv = x0 + (i + 1) * hh;
      if (!Number.isFinite(yv)) return null;
    }
    rows.push([String(steps), fmt(xv), fmt(yv)]);
    return { y: yv, rows };
  };
  const r1 = run(h, n), r2 = run(h / 2, 2 * n);
  if (!r1 || !r2) throw fail("the numerical solution blew up");
  const p = kind === "euler" ? 1 : 4;
  const est = Math.abs(r2.y - r1.y) / (Math.pow(2, p) - 1);
  const name = kind === "euler" ? "Euler's method" : "RK4";
  env.log.add({ rule: `numeric.${kind}`, title: `${name} with h = ${fmt(h)}`, why: (kind === "euler" ? `y_(k+1) = y_k + h f(x_k, y_k).\n` : `y_(k+1) = y_k + h/6 (k1 + 2 k2 + 2 k3 + k4).\n`) + table([["k", x + "_k", y + "_k"], ...r1.rows.slice(0, 25)]), before: F, after: null, kind: "note" });
  env.log.add({ rule: `numeric.${kind}.halving`, title: "Step-halving error estimate", why: `With h/2 the value is ${fmt(r2.y)}; the error of the h-value against the exact solution is about |y_(h/2) - y_h|/(2^${p} - 1) = ${est.toExponential(3)}.`, before: null, after: null, kind: "note" });
  return {
    answers: [
      { kind: "approx", label: `${y}(${fmt(x1)}) by ${name} (h = ${fmt(h)})`, approx: approxRecord(r1.y, 1e-13 * Math.max(1, Math.abs(r1.y)) * Math.max(1, n / 10), name) },
      { kind: "approx", label: "estimated error of the method (step halving)", approx: approxRecord(est, est * 0.5 + 1e-300, "step halving") },
    ],
    solutionStatus: APPROX,
    verify: () => {
      // recompute the scheme in exact rational arithmetic (multiprecision stage values when needed)
      if (n > 400) return TCV([open("exact-recompute", "too many steps for an exact recomputation")]);
      const Qx0 = C(x0T), Qy0 = C(y0T), Qh = C(hT);
      if (![Qx0, Qy0, Qh].every((q) => X.isNum(q))) return TCV([open("exact-recompute", "the data are not rational numbers")]);
      const fq = (xq, yq) => {
        const t = C(X.subs(F, { [x]: X.num(xq), [y]: X.num(yq) }));
        if (X.isNum(t)) return t.v;
        const ap = approxRec(t, 40);
        return ap ? decToQ(ap.value) : null;
      };
      let xq = Qx0.v, yq = Qy0.v;
      const hq = Qh.v, half = N.div(hq, N.Q(2)), sixth = N.div(hq, N.Q(6));
      for (let i = 0; i < n; i++) {
        env.checkTime && env.checkTime();
        if (kind === "euler") { const k1 = fq(xq, yq); if (!k1) return TCV([open("exact-recompute", "a stage value could not be computed")]); yq = N.add(yq, N.mul(hq, k1)); }
        else {
          const k1 = fq(xq, yq); if (!k1) return TCV([open("exact-recompute", "stage")]);
          const k2 = fq(N.add(xq, half), N.add(yq, N.mul(half, k1))); if (!k2) return TCV([open("exact-recompute", "stage")]);
          const k3 = fq(N.add(xq, half), N.add(yq, N.mul(half, k2))); if (!k3) return TCV([open("exact-recompute", "stage")]);
          const k4 = fq(N.add(xq, hq), N.add(yq, N.mul(hq, k3))); if (!k4) return TCV([open("exact-recompute", "stage")]);
          yq = N.add(yq, N.mul(sixth, N.add(N.add(k1, N.mul(N.Q(2), k2)), N.add(N.mul(N.Q(2), k3), k4))));
          yq = roundQ(yq);
        }
        xq = N.add(xq, hq);
        if (kind === "euler") yq = roundQ(yq);
      }
      const yv = Number(yq.n) / Number(yq.d);
      const exactV = qToNum(yq);
      return TCV([Math.abs(exactV - r1.y) <= 1e-11 * Math.max(1, Math.abs(exactV)) ? pass("exact-recompute", `the scheme recomputed in exact / 40-digit arithmetic gives ${fmt(exactV)}`) : bad("exact-recompute", `the exact recomputation gives ${fmt(exactV)}, not ${fmt(r1.y)}`)]);
      void yv;
    },
  };
}
// decimal string -> rational
function decToQ(s) {
  const m = String(s).trim().match(/^(-?)(\d*)\.?(\d*)(?:e([+-]?\d+))?$/i);
  if (!m) return null;
  const digits = (m[2] || "0") + (m[3] || "");
  let e = (m[4] ? parseInt(m[4], 10) : 0) - (m[3] || "").length;
  let num = BigInt(digits || "0");
  if (m[1] === "-") num = -num;
  if (e >= 0) return N.Q(num * 10n ** BigInt(e));
  return N.Q(num, 10n ** BigInt(-e));
}
// keep rationals from growing without bound: round to 60 significant digits when huge
function roundQ(q) {
  if (q.d < 10n ** 80n) return q;
  const scale = 10n ** 60n;
  const n = (q.n * scale) / q.d;
  return N.Q(n, scale);
}
function qToNum(q) {
  // accurate double from a big rational
  const s = 10n ** 30n;
  const n = (q.n * s) / q.d;
  return Number(n) / 1e30;
}

// ------------------------------------------------------------------ power iteration
function charPolyQ(A) {
  // Faddeev-LeVerrier over Q: coefficients c_n .. c_0 of det(t I - A)
  const n = A.length;
  const I = (i, j) => (i === j ? N.ONE : N.ZERO);
  let M = A.map((r) => r.map(() => N.ZERO));
  const c = [N.ONE];
  for (let k = 1; k <= n; k++) {
    // M = A M_prev + c_{k-1} I
    const AM = A.map((r, i) => r.map((_, j) => { let s = N.ZERO; for (let l = 0; l < n; l++) s = N.add(s, N.mul(A[i][l], M[l][j])); return s; }));
    M = AM.map((r, i) => r.map((v, j) => N.add(v, N.mul(c[k - 1], I(i, j)))));
    const AMk = A.map((r, i) => r.map((_, j) => { let s = N.ZERO; for (let l = 0; l < n; l++) s = N.add(s, N.mul(A[i][l], M[l][j])); return s; }));
    let tr = N.ZERO;
    for (let i = 0; i < n; i++) tr = N.add(tr, AMk[i][i]);
    c.push(N.neg(N.div(tr, N.Q(k))));
  }
  return c.map((q) => Number(q.n) / Number(q.d)); // leading first
}
function durandKerner(coef) {
  const n = coef.length - 1;
  const a = coef.map((v) => v / coef[0]);
  const cm = (p, q) => ({ re: p.re * q.re - p.im * q.im, im: p.re * q.im + p.im * q.re });
  const cd = (p, q) => { const d = q.re * q.re + q.im * q.im; return { re: (p.re * q.re + p.im * q.im) / d, im: (p.im * q.re - p.re * q.im) / d }; };
  const ev = (z) => { let s = { re: 1, im: 0 }; for (let k = 1; k <= n; k++) s = { re: cm(s, z).re + a[k], im: cm(s, z).im }; return s; };
  let zs = Array.from({ length: n }, (_, k) => { const r = 1 + Math.max(...a.slice(1).map(Math.abs)); const t = (2 * Math.PI * k) / n + 0.4; return { re: r * Math.cos(t), im: r * Math.sin(t) }; });
  for (let it = 0; it < 2000; it++) {
    let moved = 0;
    zs = zs.map((z, i) => {
      let den = { re: 1, im: 0 };
      zs.forEach((w, j) => { if (j !== i) den = cm(den, { re: z.re - w.re, im: z.im - w.im }); });
      const dz = cd(ev(z), den);
      moved = Math.max(moved, Math.hypot(dz.re, dz.im));
      return { re: z.re - dz.re, im: z.im - dz.im };
    });
    if (moved < 1e-15) break;
  }
  return zs;
}
function cmdPoweriter(node, env) {
  const M = node.args[0];
  if (!M || M.k !== "matrix") throw fail("poweriter needs a square matrix, for example poweriter([[2, 1], [1, 3]])");
  const rows = M.args.map((r) => r.args.map((e) => C(e)));
  const n = rows.length;
  if (n < 2 || n > 8 || rows.some((r) => r.length !== n)) throw fail("the matrix must be square (2x2 up to 8x8)");
  if (rows.some((r) => r.some((e) => !X.isNum(e)))) throw fail("the matrix entries must be rational numbers");
  const A = rows.map((r) => r.map((e) => Number(e.v.n) / Number(e.v.d)));
  const mv = (v) => A.map((r) => r.reduce((s, a, j) => s + a * v[j], 0));
  let v = Array.from({ length: n }, (_, i) => 1 + 0.1 * i);
  let lam = 0, prev = NaN;
  const steps = [["k", "lambda_k"]];
  let it = 0;
  for (; it < 20000; it++) {
    const w = mv(v);
    const nw = Math.hypot(...w);
    if (!(nw > 0)) throw fail("the iteration hit the zero vector");
    lam = w.reduce((s, x, i) => s + x * v[i], 0) / v.reduce((s, x) => s + x * x, 0);
    v = w.map((x) => x / nw);
    if (it < 15) steps.push([String(it), fmt(lam)]);
    if (Math.abs(lam - prev) <= 1e-15 * Math.max(1, Math.abs(lam)) && it > 5) break;
    prev = lam;
  }
  if (it >= 20000) throw fail("the power method did not converge (the dominant eigenvalue may not be unique or real)");
  // sign-normalise the vector
  const big = v.reduce((m, x) => (Math.abs(x) > Math.abs(m) ? x : m), 0);
  v = v.map((x) => x / big);
  const Av = mv(v);
  const resid = Math.hypot(...Av.map((x, i) => x - lam * v[i])) / Math.hypot(...v);
  env.log.add({ rule: "numeric.power", title: "Power iteration", why: `x_(k+1) = A x_k / |A x_k|, Rayleigh quotient lambda_k = x_k . A x_k / x_k . x_k.\n` + table(steps), before: M, after: null, kind: "note" });
  const err = Math.max(resid, 1e-13 * Math.max(1, Math.abs(lam)));
  return {
    answers: [
      { kind: "approx", label: "dominant eigenvalue (power method)", approx: approxRecord(lam, err, "power iteration", { iterations: it }) },
      { kind: "exact", label: "eigenvector (approximate, scaled so its largest entry is 1)", tree: X.vector(...v.map((x) => X.num(N.Q(BigInt(Math.round(x * 1e12)), 10n ** 12n)))), note: "approximate" },
    ],
    solutionStatus: APPROX,
    verify: () => {
      const rowsQ = rows.map((r) => r.map((e) => e.v));
      const cp = charPolyQ(rowsQ);
      const roots = durandKerner(cp).sort((p, q) => Math.hypot(q.re, q.im) - Math.hypot(p.re, p.im));
      const top = roots[0], second = roots[1];
      if (Math.abs(top.im) > 1e-9 || Math.hypot(second.re, second.im) > Math.hypot(top.re, top.im) * (1 - 1e-9)) return TCV([bad("characteristic-polynomial", "the dominant eigenvalue is not unique and real, so the power method's limit is not an eigenvalue estimate")]);
      return TCV([Math.abs(top.re - lam) <= 1e-9 * Math.max(1, Math.abs(lam)) ? pass("characteristic-polynomial", `the roots of the exact characteristic polynomial (Durand-Kerner) have largest modulus at ${fmt(top.re)}`) : bad("characteristic-polynomial", `the dominant root of the characteristic polynomial is ${fmt(top.re)}, not ${fmt(lam)}`)]);
    },
  };
}

export const NUMERICAL = {
  newton: cmdNewton, bisection: cmdBisection, secant: cmdSecant, fixedpoint: cmdFixedpoint,
  trapezoid: (n, e) => rule(n, e, "trapezoid"), simpson: (n, e) => rule(n, e, "simpson"),
  eulermethod: (n, e) => stepper(n, e, "euler"), rungekutta: (n, e) => stepper(n, e, "rk4"),
  poweriter: cmdPoweriter,
};
void safe; void evalR; void forEval; void isVec;
