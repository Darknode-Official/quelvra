// Quelvra research lab: the Riemann zeta function and its nontrivial zeros.
//
// * zeta(s): Euler-Maclaurin summation (complex double precision), functional equation for Re s < 0.
// * theta(t), Z(t): Hardy's Z function, real on the real line, |Z(t)| = |zeta(1/2 + i t)|.
//   Z is computed by Euler-Maclaurin for small t and by the Riemann-Siegel formula with the remainder
//   terms C0..C4 for large t. The C_k come from the Taylor series of Psi(p) = cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p),
//   whose coefficients are computed once in 400-bit arithmetic (bigfloat.js) to avoid the instability of
//   dividing power series in double precision.
// * zetaZeros(T): sign changes of Z between Gram points (Rosser blocks refined where Gram's law fails),
//   Brent refinement, and two independent counts of ALL zeros with 0 < Im s < T: the Riemann-von Mangoldt
//   formula N(T) = theta(T)/pi + 1 + S(T) with S(T) from the argument principle, and Turing's method (Brent's form).
//   If the number of sign changes equals N(T) then every zero up to height T is on the critical line and simple.
//   This is double-precision floating point, not interval arithmetic: it is strong numerical EVIDENCE, and the
//   Riemann hypothesis remains open.

import * as B from "../bigfloat.js";
import { asBudget, budgetError } from "./budget.js";

const PI = Math.PI, TWO_PI = 2 * Math.PI, LN_PI = Math.log(Math.PI);
export const ZEROS_T_MAX = 1e6;

// ------------------------------------------------------------------ complex helpers ([re, im])
const cadd = (a, b) => [a[0] + b[0], a[1] + b[1]];
const cmul = (a, b) => [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]];
const cdiv = (a, b) => { const d = b[0] * b[0] + b[1] * b[1]; return [(a[0] * b[0] + a[1] * b[1]) / d, (a[1] * b[0] - a[0] * b[1]) / d]; };
const cexp = (a) => { const m = Math.exp(a[0]); return [m * Math.cos(a[1]), m * Math.sin(a[1])]; };
const clog = (a) => [Math.log(Math.hypot(a[0], a[1])), Math.atan2(a[1], a[0])];
const cabs = (a) => Math.hypot(a[0], a[1]);
const csin = (a) => [Math.sin(a[0]) * Math.cosh(a[1]), Math.cos(a[0]) * Math.sinh(a[1])];
// n^(-s) for real n > 0
const npow = (lnN, s) => { const m = Math.exp(-s[0] * lnN), ph = -s[1] * lnN; return [m * Math.cos(ph), m * Math.sin(ph)]; };

// Bernoulli numbers B_2k / (2k)! for Euler-Maclaurin and Stirling
const B2K = [1 / 6, -1 / 30, 1 / 42, -1 / 30, 5 / 66, -691 / 2730, 7 / 6, -3617 / 510, 43867 / 798, -174611 / 330, 854513 / 138, -236364091 / 2730, 8553103 / 6, -23749461029 / 870];
const FACT = [1]; for (let i = 1; i <= 30; i++) FACT.push(FACT[i - 1] * i);

// log Gamma(z) on the principal (continuous) branch, complex z with Re z > 0
export function lnGamma(z) {
  let acc = [0, 0], w = [z[0], z[1]];
  while (w[0] < 12) { acc = cadd(acc, clog(w)); w = [w[0] + 1, w[1]]; }
  const lw = clog(w);
  let r = cadd(cmul([w[0] - 0.5, w[1]], lw), [-w[0] + 0.5 * Math.log(TWO_PI), -w[1]]);
  let wp = w; const w2 = cmul(w, w);
  for (let k = 1; k <= 8; k++) { r = cadd(r, cdiv([B2K[k - 1] / (2 * k * (2 * k - 1)), 0], wp)); wp = cmul(wp, w2); }
  return [r[0] - acc[0], r[1] - acc[1]];
}
function cgamma(z) {
  if (z[0] < 0.5) { // reflection
    const s = csin([PI * z[0], PI * z[1]]);
    return cdiv([PI, 0], cmul(s, cgamma([1 - z[0], -z[1]])));
  }
  return cexp(lnGamma(z));
}

// ------------------------------------------------------------------ zeta(s) by Euler-Maclaurin
export function zetaEM(s) {
  if (s[0] === 1 && s[1] === 0) throw budgetError("DOMAIN", "zeta has a pole at s = 1");
  const as = cabs(s);
  const N = Math.max(12, Math.ceil(as + 10));
  let sum = [0, 0];
  for (let n = 1; n < N; n++) sum = cadd(sum, npow(Math.log(n), s));
  const lnN = Math.log(N);
  const Ns = npow(lnN, s);                              // N^-s
  sum = cadd(sum, cdiv(cmul(Ns, [N, 0]), [s[0] - 1, s[1]])); // N^(1-s)/(s-1)
  sum = cadd(sum, [Ns[0] / 2, Ns[1] / 2]);
  let poch = [s[0], s[1]];                               // s (s+1) ... (s+2k-2)
  let pw = [Ns[0] / N, Ns[1] / N];                        // N^(-s-2k+1)
  for (let k = 1; k <= 12; k++) {
    const c = B2K[k - 1] / FACT[2 * k];
    const term = cmul(poch, pw);
    sum = cadd(sum, [c * term[0], c * term[1]]);
    poch = cmul(poch, cmul([s[0] + 2 * k - 1, s[1]], [s[0] + 2 * k, s[1]]));
    pw = [pw[0] / (N * N), pw[1] / (N * N)];
  }
  return sum;
}
// zeta(s) for any complex s != 1 (functional equation for Re s < 0)
export function zeta(s) {
  if (typeof s === "number") s = [s, 0];
  if (s[0] < 0) {
    if (s[1] === 0 && Number.isInteger(s[0]) && s[0] % 2 === 0) return [0, 0]; // trivial zeros, exactly
    // zeta(s) = 2^s pi^(s-1) sin(pi s / 2) Gamma(1-s) zeta(1-s)
    const one = [1 - s[0], -s[1]];
    const f = cmul(cmul(cexp([s[0] * Math.LN2, s[1] * Math.LN2]), cexp([(s[0] - 1) * LN_PI, s[1] * LN_PI])), csin([PI * s[0] / 2, PI * s[1] / 2]));
    return cmul(cmul(f, cgamma(one)), zetaEM(one));
  }
  return zetaEM(s);
}

// ------------------------------------------------------------------ theta and Z
export function theta(t) {
  if (t >= 30) {
    const it = 1 / t, it2 = it * it;
    return t / 2 * Math.log(t / TWO_PI) - t / 2 - PI / 8 + it * (1 / 48 + it2 * (7 / 5760 + it2 * (31 / 80640 + it2 * (127 / 430080 + it2 * 511 / 1216512))));
  }
  return lnGamma([0.25, t / 2])[1] - t / 2 * LN_PI;
}
// theta'(t) (for Newton on Gram points)
const thetaPrime = (t) => 0.5 * Math.log(t / TWO_PI) + (t > 5 ? -1 / (48 * t * t) : 0);

// Riemann-Siegel remainder coefficients: Psi Taylor series in x = p - 1/2, computed in high precision.
let PSI = null;
function psiCoefficients(K = 110, prec = 420) {
  const pi = B.pi(prec), twoPi = B.mulPow2(pi, 1);
  const a = B.mul(pi, B.div(B.fromInt(5), B.fromInt(8), prec), prec);   // 5 pi / 8
  const [s5, c5] = B.sincos(a, prec);
  // f(x) = cos(2 pi x^2 - 5 pi/8) = c5 cos(2 pi x^2) + s5 sin(2 pi x^2)
  const f = new Array(K + 1).fill(B.ZERO), g = new Array(K + 1).fill(B.ZERO);
  let pw = B.ONE, fct = B.ONE;
  for (let m = 0; 2 * m <= K; m++) {        // (2 pi)^m / m! times x^(2m)
    const term = B.div(pw, fct, prec);
    if (2 * m <= K) {
      // cos(2 pi y) and sin(2 pi y) with y = x^2: term index m, y^m = x^(2m)
      if (m % 2 === 0) f[2 * m] = B.mul(term, (m / 2) % 2 === 0 ? c5 : B.neg(c5), prec);
      else f[2 * m] = B.mul(term, ((m - 1) / 2) % 2 === 0 ? s5 : B.neg(s5), prec);
      // g(x) = -cos(2 pi x): coefficient of x^m (m even)
      if (m % 2 === 0 && m <= K) g[m] = B.neg(B.mul(term, (m / 2) % 2 === 0 ? B.ONE : B.neg(B.ONE), prec));
    }
    pw = B.mul(pw, twoPi, prec); fct = B.mul(fct, B.fromInt(m + 1), prec);
  }
  for (let m = 2 * Math.floor(K / 2) + 2; m <= K; m++) g[m] = B.ZERO;
  // c = f / g by series division
  const c = [];
  for (let k = 0; k <= K; k++) {
    let acc = f[k];
    for (let j = 0; j < k; j++) if (!B.isZero(g[k - j])) acc = B.sub(acc, B.mul(c[j], g[k - j], prec), prec);
    c.push(B.div(acc, g[0], prec));
  }
  return c.map((v) => B.toNumber(v));
}
// Psi^{(j)}(p) from the series
function psiDeriv(x, j) {
  const c = PSI;
  let s = 0;
  for (let k = c.length - 1; k >= j; k--) {
    let f = 1; for (let i = 0; i < j; i++) f *= k - i;
    s = s * x + c[k] * f;
  }
  return s;
}
function rsCoefficients(p) {
  if (!PSI) PSI = psiCoefficients();
  const x = p - 0.5;
  const d = (j) => psiDeriv(x, j);
  const pi2 = PI * PI, pi4 = pi2 * pi2, pi6 = pi4 * pi2, pi8 = pi4 * pi4;
  const C0 = d(0);
  const C1 = -d(3) / (96 * pi2);
  const C2 = d(2) / (64 * pi2) + d(6) / (18432 * pi4);
  const C3 = -d(1) / (64 * pi2) - d(5) / (3840 * pi4) - d(9) / (5308416 * pi6);
  const C4 = d(0) / (128 * pi2) + 19 * d(4) / (24576 * pi4) + 11 * d(8) / (5898240 * pi6) + d(12) / (2038431744 * pi8);
  return [C0, C1, C2, C3, C4];
}
export function ZRS(t, terms = 5) {
  const a = Math.sqrt(t / TWO_PI);
  const N = Math.floor(a), p = a - N;
  const th = theta(t);
  let s = 0;
  for (let n = 1; n <= N; n++) s += Math.cos(th - t * Math.log(n)) / Math.sqrt(n);
  const C = rsCoefficients(p);
  let R = 0, ap = 1;
  for (let k = 0; k < terms; k++) { R += C[k] * ap; ap /= a; }
  return 2 * s + (N % 2 === 1 ? 1 : -1) * R / Math.sqrt(a);
}
export function ZEM(t) {
  const z = zetaEM([0.5, t]);
  const th = theta(t);
  return Math.cos(th) * z[0] - Math.sin(th) * z[1];
}
export const RS_THRESHOLD = 400;
export const Z = (t) => (t < RS_THRESHOLD ? ZEM(t) : ZRS(t));

// ------------------------------------------------------------------ Gram points, Brent
export function gramPoint(n, guess) {
  let t = guess || (n < 1 ? 17.8 : TWO_PI * Math.exp(1 + lambertW((8 * n + 1) / (8 * Math.E))));
  for (let i = 0; i < 60; i++) {
    const dt = (theta(t) - n * PI) / thetaPrime(t);
    t -= dt;
    if (t < 7) t = 7;
    if (Math.abs(dt) < 1e-13 * t) break;
  }
  return t;
}
function lambertW(x) { let w = Math.log(1 + x); for (let i = 0; i < 50; i++) { const e = Math.exp(w); const d = (w * e - x) / (e * (w + 1)); w -= d; if (Math.abs(d) < 1e-15) break; } return w; }

export function brent(f, a, b, fa, fb, tol = 1e-13, maxIter = 100) {
  if (fa === 0) return a; if (fb === 0) return b;
  if (fa * fb > 0) throw new Error("brent: no sign change");
  let c = a, fc = fa, d = b - a, e = d;
  for (let i = 0; i < maxIter; i++) {
    if (fb * fc > 0) { c = a; fc = fa; d = e = b - a; }
    if (Math.abs(fc) < Math.abs(fb)) { a = b; b = c; c = a; fa = fb; fb = fc; fc = fa; }
    const tol1 = 2 * Number.EPSILON * Math.abs(b) + tol / 2, m = (c - b) / 2;
    if (Math.abs(m) <= tol1 || fb === 0) return b;
    if (Math.abs(e) >= tol1 && Math.abs(fa) > Math.abs(fb)) {
      let p, q, r; const s = fb / fa;
      if (a === c) { p = 2 * m * s; q = 1 - s; }
      else { q = fa / fc; r = fb / fc; p = s * (2 * m * q * (q - r) - (b - a) * (r - 1)); q = (q - 1) * (r - 1) * (s - 1); }
      if (p > 0) q = -q; else p = -p;
      if (2 * p < Math.min(3 * m * q - Math.abs(tol1 * q), Math.abs(e * q))) { e = d; d = p / q; } else { d = m; e = d; }
    } else { d = m; e = d; }
    a = b; fa = fb;
    b += Math.abs(d) > tol1 ? d : (m > 0 ? tol1 : -tol1);
    fb = f(b);
  }
  return b;
}

// ------------------------------------------------------------------ N(T) via the argument principle
// S(T) = arg zeta(1/2 + i T) / pi, the argument obtained by continuous variation along 2 -> 2 + iT -> 1/2 + iT.
// On Re s = 2, |zeta(s) - 1| <= zeta(2) - 1 < 1, so the principal argument is correct there.
export function rvmCount(T, budget) {
  let sigma = 2, z = zeta([2, T]);
  let arg = Math.atan2(z[1], z[0]);
  let h = 0.05, iter = 0;
  while (sigma > 0.5) {
    const s2 = Math.max(0.5, sigma - h);
    const z2 = zeta([s2, T]);
    const d = Math.atan2(z[0] * z2[1] - z[1] * z2[0], z[0] * z2[0] + z[1] * z2[1]); // arg(z2 / z)
    const ratio = cabs(z2) / cabs(z);
    if ((Math.abs(d) > 0.25 || ratio > 3 || ratio < 1 / 3) && h > 1e-7) { h /= 2; continue; }
    arg += d; z = z2; sigma = s2; if (h < 0.05) h *= 1.5;
    if (budget) budget.tick(Math.ceil(T) + 20);
    if (++iter > 100000) throw budgetError("BUDGET", "argument tracking did not converge");
  }
  const est = theta(T) / PI + 1 + arg / PI;
  return { estimate: est, count: Math.round(est), S: arg / PI, distance: Math.abs(est - Math.round(est)), steps: iter };
}

// ------------------------------------------------------------------ the zero search
export function zetaZeros(T = 1000, opts = {}) {
  const budget = asBudget(opts, "zeta zero search");
  T = Number(T);
  if (!(T > 0)) throw budgetError("UNSUPPORTED", "T must be positive");
  if (T > ZEROS_T_MAX) throw budgetError("BUDGET", `T is capped at ${ZEROS_T_MAX}`);
  const Zf = (t) => { budget.tick(t < RS_THRESHOLD ? Math.ceil(t) + 30 : Math.ceil(Math.sqrt(t / TWO_PI)) + 20); return Z(t); };
  // Gram points g_n for n = -1 .. beyond T, plus extra blocks for Turing's method
  const gram = [];                   // {n, t, z, good}
  let n = -1, g = gramPoint(-1, 9.6);
  const extraBlocks = 6;
  let goodAfterT = 0;
  while (true) {
    const z = Zf(g);
    const good = (n % 2 === 0 ? 1 : -1) * z > 0;
    gram.push({ n, t: g, z, good });
    if (g > T && good) { goodAfterT++; if (goodAfterT > extraBlocks) break; }
    n++;
    g = gramPoint(n, g + PI / thetaPrime(g));
    if (gram.length % 256 === 0) budget.progress(Math.min(1, g / T) * 0.4, "zeta: Gram points");
  }
  // Gram blocks between consecutive good Gram points; Rosser's rule: block [g_j, g_k) contains >= k - j sign changes
  const brackets = [];               // [a, b, za, zb]
  const blocks = [];
  let violations = 0, rosserFailures = [];
  // below the first good Gram point (g_-1 = 9.667 is good): Z has no zeros on (0, g_-1]
  let j = 0;
  while (j < gram.length - 1) {
    let k = j + 1;
    while (k < gram.length && !gram[k].good) k++;
    if (k >= gram.length) break;
    const want = k - j;
    const pts = gram.slice(j, k + 1).map((q) => [q.t, q.z]);
    let changes = countChanges(pts);
    let depth = 0;
    let cur = pts;
    while (changes < want && depth < 8) {    // refine: insert midpoints
      depth++;
      const nxt = [cur[0]];
      for (let i = 1; i < cur.length; i++) { const m = (cur[i - 1][0] + cur[i][0]) / 2; nxt.push([m, Zf(m)], cur[i]); }
      cur = nxt; changes = countChanges(cur);
    }
    if (want > 1) violations++;
    blocks.push({ from: gram[j].n, to: gram[k].n, length: want, changes, rosser: changes >= want });
    if (changes < want) rosserFailures.push({ from: gram[j].t, to: gram[k].t, want, found: changes });
    for (let i = 1; i < cur.length; i++) if (Math.sign(cur[i - 1][1]) !== Math.sign(cur[i][1])) brackets.push([cur[i - 1][0], cur[i][0], cur[i - 1][1], cur[i][1]]);
    j = k;
  }
  // refine every bracket below T (and just above, for the Turing count)
  const zeros = [];
  for (let i = 0; i < brackets.length; i++) {
    const [a, b, za, zb] = brackets[i];
    if (a >= T && zeros.length && zeros[zeros.length - 1] >= T) { zeros.push((a + b) / 2); continue; }
    const tol = Math.max(1e-13, 4e-16 * b);
    zeros.push(brent(Zf, a, b, za, zb, tol));
    if (i % 64 === 0) budget.progress(0.4 + 0.5 * (i / brackets.length), "zeta: refining zeros");
  }
  const below = zeros.filter((t) => t < T);
  // count 1: Riemann-von Mangoldt with the argument principle at T (nudged off any zero)
  let Tc = T;
  const prevZ = below.length ? below[below.length - 1] : -Infinity, nextZ = zeros[below.length] ?? Infinity;
  if (T - prevZ < 1e-3 || nextZ - T < 1e-3) Tc = (T - prevZ < nextZ - T) ? (prevZ + Math.min(nextZ, T + 0.5)) / 2 : (Math.max(prevZ, T - 0.5) + nextZ) / 2;
  const rvm = rvmCount(Tc, budget);
  const signChangesBelowTc = zeros.filter((t) => t < Tc).length;
  // (Tc differs from T only when a zero lies within 1e-3 of T; then Tc is moved to the midpoint of the gap on the far side.)
  // count 2: Turing's method in Brent's form at the last good Gram point g_m <= T followed by enough Rosser blocks
  const turing = turingCheck(gram, blocks, zeros, T);
  const certified = rvm.count === signChangesBelowTc && rvm.distance < 0.25;
  budget.progress(1, "zeta zeros");
  return {
    T, zeros: below, count: below.length,
    rvm: { T: Tc, count: rvm.count, estimate: rvm.estimate, S: rvm.S, residual: rvm.distance },
    turing, gramPoints: gram.length, gramBlocks: blocks.length, gramLawViolations: violations, rosserFailures,
    allOnCriticalLine: certified && rosserFailures.length === 0,
    method: `Z(t) by ${T < RS_THRESHOLD ? "Euler-Maclaurin" : "Euler-Maclaurin below t = 400 and Riemann-Siegel (C0..C4) above"}; sign changes between Gram points; Brent refinement; N(T) by the argument principle; Turing's method (Brent's form)`,
    precision: "IEEE double precision (not interval arithmetic)",
    ms: budget.elapsed(),
  };
}
function countChanges(pts) { let c = 0; for (let i = 1; i < pts.length; i++) if (Math.sign(pts[i - 1][1]) !== Math.sign(pts[i][1])) c++; return c; }

// Brent (1979): if K consecutive Gram blocks with union [g_n, g_p) satisfy Rosser's rule and
// K >= 0.0061 ln^2(g_p) + 0.08 ln(g_p), then N(g_n) <= n + 1. Combined with n + 1 sign changes found below g_n,
// N(g_n) = n + 1 exactly. We only apply it for g_n >= 168 pi (the range covered by Lehman's bound).
function turingCheck(gram, blocks, zeros, T) {
  const LO = 168 * PI;
  const tOf = new Map(gram.map((q) => [q.n, q.t]));
  const countBelow = (x) => { let lo = 0, hi = zeros.length; while (lo < hi) { const m = (lo + hi) >> 1; if (zeros[m] < x) lo = m + 1; else hi = m; } return lo; };
  // the last block start g_n <= T (and >= 168 pi) that is followed by enough consecutive Rosser blocks
  for (let bi = blocks.length - 1; bi >= 0; bi--) {
    const g0 = tOf.get(blocks[bi].from);
    if (g0 > T) continue;
    if (g0 < LO) break;
    let K = 0;
    for (let bj = bi; bj < blocks.length && blocks[bj].rosser; bj++) {
      K++;
      const gp = tOf.get(blocks[bj].to);
      const need = Math.max(1, Math.ceil(0.0061 * Math.log(gp) ** 2 + 0.08 * Math.log(gp)));
      if (K >= need) {
        const found = countBelow(g0);
        return { applied: true, gramIndex: blocks[bi].from, g: g0, blocksUsed: K, required: need, signChangesBelow: found, expected: blocks[bi].from + 1, agrees: found === blocks[bi].from + 1 };
      }
    }
  }
  return { applied: false, reason: T < LO ? "Turing's method (Brent's form) is only applied at heights >= 168 pi; the argument-principle count is used instead" : "no qualifying run of Rosser blocks found" };
}

// Known values (A. Odlyzko's tables) used only as an extra check in verification and tests.
export const KNOWN_ZEROS = [14.134725141734693790, 21.022039638771554993, 25.010857580145688763, 30.424876125859513210, 32.935061587739189691,
  37.586178158825671257, 40.918719012147495187, 43.327073280914999519, 48.005150881167159727, 49.773832477672302181];
