// Quelvra interval arithmetic over IEEE doubles with outward rounding.
//
// An interval is a plain frozen object { lo, hi, def, cont }:
//   lo <= hi (may be -Infinity / +Infinity)   the enclosure of all defined values
//   def   true when the operation chain is defined at EVERY point of the input box
//   cont  true when every operation is continuous on the input box
// The empty interval (nowhere defined) has lo = +Infinity, hi = -Infinity, def = false.
//
// Outward rounding: every elementary result is widened by one ulp (nextDown / nextUp)
// for + - * / sqrt, and by two ulps for libm functions (exp, ln, sin, ...), whose results
// are not guaranteed to be correctly rounded. The enclosure is therefore a certified
// superset of the true range as long as libm errors stay within 1 ulp (true for V8).
// Used for certified "no root here" decisions and for discontinuity / pole detection.

const F64 = new Float64Array(1);
const U64 = new BigUint64Array(F64.buffer);
export function nextUp(x) {
  if (Number.isNaN(x) || x === Infinity) return x;
  if (x === 0) return Number.MIN_VALUE;
  F64[0] = x;
  if (x > 0) U64[0] += 1n; else U64[0] -= 1n;
  return F64[0];
}
export function nextDown(x) {
  if (Number.isNaN(x) || x === -Infinity) return x;
  if (x === 0) return -Number.MIN_VALUE;
  F64[0] = x;
  if (x > 0) U64[0] -= 1n; else U64[0] += 1n;
  return F64[0];
}
const down = (x) => nextDown(x);
const up = (x) => nextUp(x);
const down2 = (x) => nextDown(nextDown(x));
const up2 = (x) => nextUp(nextUp(x));

export function I(lo, hi = lo, def = true, cont = true) {
  if (Number.isNaN(lo) || Number.isNaN(hi)) return Object.freeze({ lo: -Infinity, hi: Infinity, def: false, cont: false });
  return Object.freeze({ lo, hi, def, cont });
}
export const EMPTY = Object.freeze({ lo: Infinity, hi: -Infinity, def: false, cont: true });
export const ENTIRE = I(-Infinity, Infinity);
export const isEmpty = (a) => a.lo > a.hi;
export const point = (x) => I(x, x);
export const entire = (def = true, cont = true) => I(-Infinity, Infinity, def, cont);
export const contains = (a, x) => a.lo <= x && x <= a.hi;
export const containsZero = (a) => a.lo <= 0 && 0 <= a.hi;
export const width = (a) => a.hi - a.lo;
export const mid = (a) => (isFinite(a.lo) && isFinite(a.hi) ? a.lo + (a.hi - a.lo) / 2 : NaN);
export const hull = (a, b) => (isEmpty(a) ? b : isEmpty(b) ? a : I(Math.min(a.lo, b.lo), Math.max(a.hi, b.hi), a.def && b.def, a.cont && b.cont));
export function intersect(a, b) {
  const lo = Math.max(a.lo, b.lo), hi = Math.min(a.hi, b.hi);
  return lo > hi ? EMPTY : I(lo, hi, a.def && b.def, a.cont && b.cont);
}
// An interval enclosing a rational { n, d } (exact when the double is exact).
export function fromRational(r) {
  const x = Number(r.n) / Number(r.d);
  const exact = r.d === 1n ? Number.isSafeInteger(x) && BigInt(x) === r.n : isPow2(r.d) && Number.isSafeInteger(Number(r.n)) && Number.isFinite(x);
  if (!Number.isFinite(x)) return I(x > 0 ? Number.MAX_VALUE : -Infinity, x > 0 ? Infinity : -Number.MAX_VALUE);
  return exact ? I(x, x) : I(down(x), up(x));
}
const isPow2 = (d) => d > 0n && (d & (d - 1n)) === 0n && d < 1n << 1000n;
const fl = (a, b) => a.def && b.def;
const ct = (a, b) => a.cont && b.cont;

export function add(a, b) {
  if (isEmpty(a) || isEmpty(b)) return EMPTY;
  return I(down(a.lo + b.lo), up(a.hi + b.hi), fl(a, b), ct(a, b));
}
export function sub(a, b) {
  if (isEmpty(a) || isEmpty(b)) return EMPTY;
  return I(down(a.lo - b.hi), up(a.hi - b.lo), fl(a, b), ct(a, b));
}
export const neg = (a) => (isEmpty(a) ? EMPTY : I(-a.hi, -a.lo, a.def, a.cont));
const m0 = (x, y) => (x === 0 || y === 0 ? 0 : x * y);
export function mul(a, b) {
  if (isEmpty(a) || isEmpty(b)) return EMPTY;
  const p = [m0(a.lo, b.lo), m0(a.lo, b.hi), m0(a.hi, b.lo), m0(a.hi, b.hi)];
  return I(down(Math.min(...p)), up(Math.max(...p)), fl(a, b), ct(a, b));
}
// Division. If b contains zero the result is marked possibly-undefined and discontinuous,
// and is the hull of the extended quotient (entire when 0 is interior to b).
export function div(a, b) {
  if (isEmpty(a) || isEmpty(b)) return EMPTY;
  if (b.lo === 0 && b.hi === 0) return EMPTY;
  if (b.lo > 0 || b.hi < 0) {
    const p = [a.lo / b.lo, a.lo / b.hi, a.hi / b.lo, a.hi / b.hi].map((x) => (Number.isNaN(x) ? 0 : x));
    return I(down(Math.min(...p)), up(Math.max(...p)), fl(a, b), ct(a, b));
  }
  const parts = divSplit(a, b);
  let r = EMPTY;
  for (const p of parts) r = hull(r, p);
  return isEmpty(r) ? EMPTY : I(r.lo, r.hi, false, false);
}
// Extended division returning 0, 1 or 2 intervals (used for interval Newton).
export function divSplit(a, b) {
  if (isEmpty(a) || isEmpty(b) || (b.lo === 0 && b.hi === 0)) return [];
  if (b.lo > 0 || b.hi < 0) return [div(a, b)];
  if (a.lo <= 0 && a.hi >= 0) return [entire(false, false)];
  const flags = (lo, hi) => I(lo, hi, false, false);
  if (a.hi < 0) {
    if (b.hi === 0) return [flags(down(a.hi / b.lo), Infinity)];
    if (b.lo === 0) return [flags(-Infinity, up(a.hi / b.hi))];
    return [flags(-Infinity, up(a.hi / b.hi)), flags(down(a.hi / b.lo), Infinity)];
  }
  if (b.hi === 0) return [flags(-Infinity, up(a.lo / b.lo))];
  if (b.lo === 0) return [flags(down(a.lo / b.hi), Infinity)];
  return [flags(-Infinity, up(a.lo / b.lo)), flags(down(a.lo / b.hi), Infinity)];
}
export function abs(a) {
  if (isEmpty(a)) return EMPTY;
  if (a.lo >= 0) return a;
  if (a.hi <= 0) return neg(a);
  return I(0, Math.max(-a.lo, a.hi), a.def, a.cont);
}
export function sqr(a) { return powInt(a, 2); }
export function powInt(a, n) {
  if (isEmpty(a)) return EMPTY;
  n = Number(n);
  if (n === 0) return containsZero(a) ? I(1, 1, false, a.cont) : I(1, 1, a.def, a.cont);
  if (n < 0) return div(I(1, 1), powInt(a, -n));
  const p = (x) => (x === 0 ? 0 : x === Infinity ? Infinity : x === -Infinity ? (n % 2 ? -Infinity : Infinity) : x ** n);
  const w = (lo, hi) => I(n === 1 ? lo : down2(lo), n === 1 ? hi : up2(hi), a.def, a.cont);
  if (n % 2 === 1) return w(p(a.lo), p(a.hi));
  if (a.lo >= 0) return w(p(a.lo), p(a.hi));
  if (a.hi <= 0) return w(p(a.hi), p(a.lo));
  return I(0, up2(Math.max(p(a.lo), p(a.hi))), a.def, a.cont);
}
const rootD = (x, q) => (x === 0 ? 0 : Math.abs(x) === Infinity ? x : Math.sign(x) * (q === 3 ? Math.cbrt(Math.abs(x)) : Math.abs(x) ** (1 / q)));
// q-th root with the real convention (odd roots of negatives are real).
export function root(a, q) {
  if (isEmpty(a)) return EMPTY;
  q = Number(q);
  if (q === 1) return a;
  if (q % 2 === 0) {
    if (a.hi < 0) return EMPTY;
    const lo = Math.max(a.lo, 0);
    const def = a.def && a.lo >= 0;
    return I(Math.max(0, down2(down2(rootD(lo, q)))), up2(up2(rootD(a.hi, q))), def, a.cont);
  }
  return I(down2(down2(rootD(a.lo, q))), up2(up2(rootD(a.hi, q))), a.def, a.cont);
}
export function powRat(a, p, q) {
  p = Number(p); q = Number(q);
  if (q === 1) return powInt(a, p);
  if (p < 0) return div(I(1, 1), powRat(a, -p, q));
  return powInt(root(a, q), p);
}
export function sqrt(a) { return root(a, 2); }
export function exp(a) {
  if (isEmpty(a)) return EMPTY;
  return I(Math.max(0, down2(Math.exp(a.lo))), up2(Math.exp(a.hi)), a.def, a.cont);
}
export function ln(a) {
  if (isEmpty(a) || a.hi <= 0) return EMPTY;
  const def = a.def && a.lo > 0;
  const lo = a.lo > 0 ? down2(Math.log(a.lo)) : -Infinity;
  return I(lo, up2(Math.log(a.hi)), def, a.cont);
}
// general a^b = exp(b ln a) for a > 0
export function pow(a, b) {
  if (isEmpty(a) || isEmpty(b)) return EMPTY;
  const r = exp(mul(b, ln(a)));
  if (a.lo <= 0) return I(Math.max(0, r.lo), r.hi, false, r.cont);
  return r;
}
const HALF_PI_LO = 1.5707963267948966, TWO_PI = 6.283185307179586;
// Does the interval contain a point c + k*period for some integer k? (conservative: may say yes)
function hitsLattice(a, c, period) {
  const k0 = Math.ceil((a.lo - c) / period - 1e-9);
  const x = c + k0 * period;
  return x <= a.hi + 1e-9 * Math.max(1, Math.abs(a.hi));
}
function trig(a, f, maxAt, minAt) {
  if (isEmpty(a)) return EMPTY;
  if (!isFinite(a.lo) || !isFinite(a.hi) || a.hi - a.lo >= TWO_PI) return I(-1, 1, a.def, a.cont);
  let lo = Math.min(f(a.lo), f(a.hi)), hi = Math.max(f(a.lo), f(a.hi));
  lo = Math.max(-1, down2(lo));
  hi = Math.min(1, up2(hi));
  if (hitsLattice(a, maxAt, TWO_PI)) hi = 1;
  if (hitsLattice(a, minAt, TWO_PI)) lo = -1;
  return I(lo, hi, a.def, a.cont);
}
export const sin = (a) => trig(a, Math.sin, HALF_PI_LO, -HALF_PI_LO);
export const cos = (a) => trig(a, Math.cos, 0, Math.PI);
export function tan(a) {
  if (isEmpty(a)) return EMPTY;
  if (!isFinite(a.lo) || !isFinite(a.hi) || a.hi - a.lo >= Math.PI || hitsLattice(a, HALF_PI_LO, Math.PI)) return entire(false, false);
  return I(down2(Math.tan(a.lo)), up2(Math.tan(a.hi)), a.def, a.cont);
}
const mono = (f) => (a) => (isEmpty(a) ? EMPTY : I(down2(f(a.lo)), up2(f(a.hi)), a.def, a.cont));
export const atan = mono(Math.atan);
export const sinh = mono(Math.sinh);
export const tanh = (a) => { const r = mono(Math.tanh)(a); return isEmpty(r) ? r : I(Math.max(-1, r.lo), Math.min(1, r.hi), r.def, r.cont); };
export const asinh = mono(Math.asinh);
export const erfMono = (erf) => (a) => { const r = mono(erf)(a); return isEmpty(r) ? r : I(Math.max(-1, r.lo), Math.min(1, r.hi), r.def, r.cont); };
export function cosh(a) {
  if (isEmpty(a)) return EMPTY;
  const m = abs(a);
  return I(Math.max(1, down2(Math.cosh(m.lo))), up2(Math.cosh(m.hi)), a.def, a.cont);
}
function clipMono(f, lo0, hi0, openEnds = false) {
  return (a) => {
    if (isEmpty(a)) return EMPTY;
    const lo = Math.max(a.lo, lo0), hi = Math.min(a.hi, hi0);
    if (lo > hi || (openEnds && (lo === hi0 || hi === lo0))) return EMPTY;
    const def = a.def && a.lo >= lo0 && a.hi <= hi0 && !(openEnds && (a.lo === lo0 || a.hi === hi0));
    return I(down2(f(lo)), up2(f(hi)), def, a.cont);
  };
}
export const asin = clipMono(Math.asin, -1, 1);
export const acosRaw = clipMono((x) => -Math.acos(x), -1, 1);
export const acos = (a) => neg(acosRaw(a)); // acos is decreasing
export const acosh = clipMono(Math.acosh, 1, Infinity);
export const atanh = clipMono(Math.atanh, -1, 1, true);
function step(f) {
  return (a) => {
    if (isEmpty(a)) return EMPTY;
    const lo = f(a.lo), hi = f(a.hi);
    return I(lo, hi, a.def, a.cont && lo === hi);
  };
}
export const floor = step(Math.floor);
export const ceil = step(Math.ceil);
export const round = step(Math.round);
export function sign(a) {
  if (isEmpty(a)) return EMPTY;
  const lo = Math.sign(a.lo), hi = Math.sign(a.hi);
  return I(lo, hi, a.def, a.cont && lo === hi && !(a.lo <= 0 && a.hi >= 0 && !(a.lo === 0 && a.hi === 0)));
}
// Gamma on (0, oo): decreasing on (0, x_min), increasing on (x_min, oo). Poles at 0, -1, -2, ...
const GAMMA_XMIN = 1.4616321449683623, GAMMA_MIN = 0.8856031944108887;
export function gammaWith(g) {
  return (a) => {
    if (isEmpty(a)) return EMPTY;
    if (a.lo <= 0) {
      const onlyNegNonPole = a.hi < 0 && Math.floor(a.lo) === Math.floor(a.hi) && !Number.isInteger(a.hi) && !Number.isInteger(a.lo);
      if (!onlyNegNonPole) return entire(false, false);
      const x = g(a.lo), y = g(a.hi);
      return I(down2(down2(Math.min(x, y))), up2(up2(Math.max(x, y))), a.def, a.cont);
    }
    const x = g(a.lo), y = g(a.hi);
    let lo, hi;
    if (a.lo >= GAMMA_XMIN) { lo = x; hi = y; }
    else if (a.hi <= GAMMA_XMIN) { lo = y; hi = x; }
    else { lo = GAMMA_MIN * (1 - 1e-15); hi = Math.max(x, y); }
    // widen generously: the double gamma is accurate to ~1e-14 relative
    return I(lo - Math.abs(lo) * 1e-13, hi + Math.abs(hi) * 1e-13, a.def, a.cont);
  };
}
export function toString(a, digits = 6) {
  if (isEmpty(a)) return "[empty]";
  const f = (x) => (isFinite(x) ? Number(x.toPrecision(digits)).toString() : x > 0 ? "oo" : "-oo");
  return `[${f(a.lo)}, ${f(a.hi)}]${a.def ? "" : " (possibly undefined)"}${a.cont ? "" : " (possibly discontinuous)"}`;
}
