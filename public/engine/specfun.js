// Real double-precision special functions for the independent verifier (verify.js).
// Written separately from the integrator's own numerics so a bug in one cannot hide a bug in
// the other. Target accuracy is about 1e-13 relative (checked against mpmath in
// test/quelvra/specfun.test.js). Every function returns NaN outside its real domain.
//
//   Si, Ci, Shi, Chi, Ei, li, erfi, erfc, FresnelS, FresnelC (normalised: integrand sin(pi t^2 / 2)),
//   lambertw (principal branch W0)

const EULER = 0.5772156649015329;
const EPS = 1e-17;

// E1(z) for complex z = (re, im) by the Lentz continued fraction; valid for |z| > ~2 with re >= 0.
function e1cf(re, im) {
  // E1(z) = e^-z / (z + 1/(1 + 1/(z + 2/(1 + 2/(z + ...))))) written as the even form
  // E1(z) = e^-z * 1/(z + 1 - 1^2/(z + 3 - 2^2/(z + 5 - ...)))
  const cdiv = (a, b, c, d) => { const q = c * c + d * d; return [(a * c + b * d) / q, (b * c - a * d) / q]; };
  const tiny = 1e-300;
  let bR = re + 1, bI = im;
  let fR = bR, fI = bI;
  if (fR === 0 && fI === 0) fR = tiny;
  let cR = fR, cI = fI, dR = 0, dI = 0;
  for (let n = 1; n < 1000; n++) {
    const a = -n * n;
    bR += 2;
    // d = 1 / (b + a d)
    let tR = bR + a * dR, tI = bI + a * dI;
    if (tR === 0 && tI === 0) tR = tiny;
    [dR, dI] = cdiv(1, 0, tR, tI);
    // c = b + a / c
    const [acR, acI] = cdiv(a, 0, cR, cI);
    cR = bR + acR; cI = bI + acI;
    if (cR === 0 && cI === 0) cR = tiny;
    const delR = cR * dR - cI * dI, delI = cR * dI + cI * dR;
    const nR = fR * delR - fI * delI, nI = fR * delI + fI * delR;
    fR = nR; fI = nI;
    if (Math.abs(delR - 1) + Math.abs(delI) < 1e-16) break;
  }
  // e^-z / f
  const m = Math.exp(-re), eR = m * Math.cos(-im), eI = m * Math.sin(-im);
  return cdiv(eR, eI, fR, fI);
}

function siciSeries(x) {
  // Si = sum (-1)^n x^(2n+1) / ((2n+1)(2n+1)!), Ci = gamma + ln x + sum (-1)^n x^(2n) / (2n (2n)!)
  let si = 0, ci = 0, t = x; // t = x^(2n+1)/(2n+1)!
  for (let n = 0; n < 200; n++) {
    const s = t / (2 * n + 1);
    si += n % 2 ? -s : s;
    const t2 = t * x / (2 * n + 2); // x^(2n+2)/(2n+2)!
    const c = t2 / (2 * n + 2);
    ci += n % 2 ? c : -c;
    t = t2 * x / (2 * n + 3);
    if (Math.abs(s) < EPS * Math.abs(si) && Math.abs(c) < EPS * (Math.abs(ci) + 1)) break;
  }
  return [si, EULER + Math.log(x) + ci];
}

export function Si(x) {
  if (!Number.isFinite(x)) return Number.isNaN(x) ? NaN : Math.sign(x) * Math.PI / 2;
  if (x < 0) return -Si(-x);
  if (x === 0) return 0;
  if (x <= 4) return siciSeries(x)[0];
  const [, eI] = e1cf(0, x); // E1(ix) = -Ci(x) + i (Si(x) - pi/2)
  return Math.PI / 2 + eI;
}
export function Ci(x) {
  if (!(x > 0)) return NaN;
  if (x === Infinity) return 0;
  if (x <= 4) return siciSeries(x)[1];
  const [eR] = e1cf(0, x);
  return -eR;
}

function shichiSeries(x) {
  let sh = 0, ch = 0, t = x;
  for (let n = 0; n < 400; n++) {
    const s = t / (2 * n + 1);
    sh += s;
    const t2 = t * x / (2 * n + 2);
    const c = t2 / (2 * n + 2);
    ch += c;
    t = t2 * x / (2 * n + 3);
    if (s < EPS * Math.abs(sh) && c < EPS * (Math.abs(ch) + 1)) break;
  }
  return [sh, EULER + Math.log(x) + ch];
}

// Ei for real x != 0
export function Ei(x) {
  if (Number.isNaN(x) || x === 0) return NaN;
  if (x === Infinity) return Infinity;
  if (x === -Infinity) return 0;
  if (x < 0) {
    const y = -x;
    if (y > 1) { const [r] = e1cf(y, 0); return -r; }
    // E1(y) = -gamma - ln y - sum (-y)^n / (n n!)
    let s = 0, t = 1;
    for (let n = 1; n < 100; n++) { t *= -y / n; const term = t / n; s += term; if (Math.abs(term) < EPS) break; }
    return EULER + Math.log(y) + s;
  }
  if (x < 50) {
    let s = 0, t = 1;
    for (let n = 1; n < 500; n++) { t *= x / n; const term = t / n; s += term; if (term < EPS * s) break; }
    return EULER + Math.log(x) + s;
  }
  // asymptotic e^x / x * sum n! / x^n (terms shrink until n ~ x)
  let s = 1, t = 1;
  for (let n = 1; n < x; n++) { const nt = t * n / x; if (nt > t || nt < EPS) break; t = nt; s += t; }
  return Math.exp(x) / x * s;
}
export function li(x) {
  if (!(x > 0) || x === 1) return x === 0 ? 0 : NaN;
  return Ei(Math.log(x));
}
export function Shi(x) {
  if (x < 0) return -Shi(-x);
  if (x === 0) return 0;
  if (x <= 8) return shichiSeries(x)[0];
  return (Ei(x) - Ei(-x)) / 2;
}
export function Chi(x) {
  if (!(x > 0)) return NaN;
  if (x <= 8) return shichiSeries(x)[1];
  return (Ei(x) + Ei(-x)) / 2;
}

export function erfi(x) {
  if (x < 0) return -erfi(-x);
  let s = 0, t = x; // t = x^(2n+1)/n!
  for (let n = 0; n < 5000; n++) {
    const term = t / (2 * n + 1);
    s += term;
    if (term < EPS * s) break;
    t *= x * x / (n + 1);
    if (!Number.isFinite(t)) return Infinity;
  }
  return 2 / Math.sqrt(Math.PI) * s;
}

export function erfc(x) {
  if (Number.isNaN(x)) return NaN;
  if (x < 0) return 2 - erfc(-x);
  if (x < 0.5) {
    // 1 - erf(x) by the Maclaurin series (no cancellation problem for 0 <= x < 0.5)
    let s = 0, t = x;
    for (let n = 0; n < 400; n++) { const term = t / (2 * n + 1); s += term; if (Math.abs(term) < EPS * Math.abs(s)) break; t *= -x * x / (n + 1); }
    return 1 - 2 / Math.sqrt(Math.PI) * s;
  }
  if (x > 27) return 0;
  // continued fraction erfc(x) = e^(-x^2)/sqrt(pi) * 1/(x + (1/2)/(x + 1/(x + (3/2)/(x + ...)))) (Lentz)
  const tiny = 1e-300;
  let f = x, C = x, D = 0;
  for (let n = 1; n < 5000; n++) {
    const a = n / 2;
    D = x + a * D; if (D === 0) D = tiny; D = 1 / D;
    C = x + a / C; if (C === 0) C = tiny;
    const del = C * D;
    f *= del;
    if (Math.abs(del - 1) < 1e-16) break;
  }
  return Math.exp(-x * x) / Math.sqrt(Math.PI) / f;
}

// Fresnel integrals, normalised: S(x) = int_0^x sin(pi t^2/2) dt, C(x) = int_0^x cos(pi t^2/2) dt
const GL_X = [0.9931285991850949, 0.9639719272779138, 0.9122344282513259, 0.8391169718222188, 0.7463319064601508, 0.6360536807265150, 0.5108670019508271, 0.3737060887154195, 0.2277858511416451, 0.0765265211334973];
const GL_W = [0.0176140071391521, 0.0406014298003869, 0.0626720483341091, 0.0832767415767048, 0.1019301198172404, 0.1181945319615184, 0.1316886384491766, 0.1420961093183820, 0.1491729864726037, 0.1527533871307258];
function fresnelQuad(x, trig) {
  // composite 20-point Gauss-Legendre; panels short enough that each holds under a quarter period
  const panels = Math.max(4, Math.ceil(x * x * 2 + 8));
  const h = x / panels;
  let s = 0;
  for (let p = 0; p < panels; p++) {
    const mid = (p + 0.5) * h, half = h / 2;
    for (let k = 0; k < 10; k++) {
      const a = mid - half * GL_X[k], b = mid + half * GL_X[k];
      s += GL_W[k] * (trig(Math.PI * a * a / 2) + trig(Math.PI * b * b / 2));
    }
  }
  return s * h / 2;
}
function fresnelAsym(x) {
  // f, g auxiliary functions; C = 1/2 + f sin - g cos, S = 1/2 - f cos - g sin (x large)
  const z = Math.PI * x * x, z2 = z * z;
  let f = 1, g = 1, tf = 1, tg = 1;
  for (let m = 1; m < 40; m++) {
    const nf = -tf * (4 * m - 3) * (4 * m - 1) / z2;
    const ng = -tg * (4 * m - 1) * (4 * m + 1) / z2;
    if (Math.abs(nf) > Math.abs(tf) || Math.abs(nf) < EPS) break;
    tf = nf; tg = ng; f += tf; g += tg;
  }
  f /= Math.PI * x;
  g /= Math.PI * x * z;
  const a = z / 2, s = Math.sin(a), c = Math.cos(a);
  return [0.5 - f * c - g * s, 0.5 + f * s - g * c]; // [S, C]
}
function fresnel(x, which) {
  if (Number.isNaN(x)) return NaN;
  if (x < 0) return -fresnel(-x, which);
  if (x === Infinity) return 0.5;
  if (x <= 1.5) {
    // series: S = sum (-1)^n (pi/2)^(2n+1) x^(4n+3) / ((2n+1)! (4n+3)), C = sum (-1)^n (pi/2)^(2n) x^(4n+1) / ((2n)! (4n+1))
    const u = Math.PI / 2 * x * x;
    let s = 0, t = which === "S" ? u : 1; // t = u^k / k!
    let k = which === "S" ? 1 : 0;
    for (let i = 0; i < 200; i++) {
      const term = t / (2 * k + 1);
      s += (Math.floor(k / 2) % 2 ? -term : term);
      t *= u * u / ((k + 1) * (k + 2));
      k += 2;
      if (Math.abs(term) < EPS * Math.abs(s)) break;
    }
    return x * s;
  }
  if (x >= 7) return fresnelAsym(x)[which === "S" ? 0 : 1];
  return fresnelQuad(x, which === "S" ? Math.sin : Math.cos);
}
export const FresnelS = (x) => fresnel(x, "S");
export const FresnelC = (x) => fresnel(x, "C");

// Lambert W, principal branch, real x >= -1/e
export function lambertw(x) {
  const branch = -1 / Math.E;
  if (Number.isNaN(x) || x < branch - 1e-15) return NaN;
  if (x === Infinity) return Infinity;
  if (x === 0) return 0;
  if (Math.abs(x - branch) < 1e-15) return -1;
  let w;
  if (x < -0.3) { const p = Math.sqrt(2 * (Math.E * x + 1)); w = -1 + p - p * p / 3 + 11 / 72 * p * p * p; }
  else if (x < 3) w = Math.log1p(x) * (1 - Math.log1p(Math.log1p(x)) / (2 + Math.log1p(x)));
  else { const l = Math.log(x); w = l - Math.log(l); }
  for (let i = 0; i < 60; i++) {
    const e = Math.exp(w), f = w * e - x;
    const d = e * (w + 1) - (w + 2) * f / (2 * w + 2);
    const nw = w - f / d;
    if (Math.abs(nw - w) <= 1e-16 * Math.max(1, Math.abs(nw))) { w = nw; break; }
    w = nw;
  }
  return w;
}

export const SPECIAL_REAL = { Si, Ci, Shi, Chi, Ei, li, erfi, erfc, FresnelS, FresnelC, lambertw, LambertW: lambertw };
