// Quelvra grapher: an independent canvas plotter for math trees.
//
// Pure parts (importable in Node, no DOM): compile, compileEnv, niceTicks, sampleFunction,
// implicitCurve, inequalityGrid, sampleParametric, samplePolar, classifyPlot.
// DOM part: createGraph(container) builds the interactive plot.
//
// Evaluation uses JavaScript doubles. That is correct here: plotting is approximation by
// nature and never feeds back into exact results. No eval / new Function: trees are walked
// once into closures.

import * as X from "./engine/expr.js";
import * as N from "./engine/num.js";
import { toText } from "./engine/print.js";

// ---------------------------------------------------------------- special functions
const LANCZOS = [
  0.99999999999980993, 676.5203681218851, -1259.1392167224028, 771.32342877765313,
  -176.61502916214059, 12.507343278686905, -0.13857109526572012, 9.9843695780195716e-6,
  1.5056327351493116e-7,
];
export function gamma(z) {
  if (!Number.isFinite(z)) return z === Infinity ? Infinity : NaN;
  if (z <= 0 && Number.isInteger(z)) return NaN; // poles
  if (z < 0.5) return Math.PI / (Math.sin(Math.PI * z) * gamma(1 - z));
  z -= 1;
  let a = LANCZOS[0];
  const t = z + 7.5;
  for (let i = 1; i < 9; i++) a += LANCZOS[i] / (z + i);
  return Math.sqrt(2 * Math.PI) * Math.pow(t, z + 0.5) * Math.exp(-t) * a;
}
function erf(x) {
  // Abramowitz and Stegun 7.1.26 (|error| < 1.5e-7): ample for plotting
  const s = x < 0 ? -1 : 1;
  const ax = Math.abs(x);
  const t = 1 / (1 + 0.3275911 * ax);
  const y = 1 - ((((1.061405429 * t - 1.453152027) * t + 1.421413741) * t - 0.284496736) * t + 0.254829592) * t * Math.exp(-ax * ax);
  return s * y;
}
const factorial = (n) => (n < 0 && Number.isInteger(n) ? NaN : Number.isInteger(n) && n <= 170 ? intFact(n) : gamma(n + 1));
function intFact(n) {
  let r = 1;
  for (let i = 2; i <= n; i++) r *= i;
  return r;
}

const FN1 = {
  sin: Math.sin, cos: Math.cos, tan: Math.tan,
  cot: (x) => 1 / Math.tan(x), sec: (x) => 1 / Math.cos(x), csc: (x) => 1 / Math.sin(x),
  asin: Math.asin, acos: Math.acos, atan: Math.atan,
  acot: (x) => (x === 0 ? Math.PI / 2 : Math.atan(1 / x)),
  asec: (x) => Math.acos(1 / x), acsc: (x) => Math.asin(1 / x),
  sinh: Math.sinh, cosh: Math.cosh, tanh: Math.tanh,
  coth: (x) => 1 / Math.tanh(x), sech: (x) => 1 / Math.cosh(x), csch: (x) => 1 / Math.sinh(x),
  asinh: Math.asinh, acosh: Math.acosh, atanh: Math.atanh,
  ln: Math.log, exp: Math.exp, abs: Math.abs, sign: Math.sign,
  floor: Math.floor, ceil: Math.ceil, round: Math.round,
  sqrt: Math.sqrt, cbrt: Math.cbrt, factorial, gamma, erf,
  re: (x) => x, im: () => 0, conj: (x) => x,
};
const FN2 = {
  mod: (a, b) => (b === 0 ? NaN : ((a % b) + b) % b),
  root: (a, n) => (a < 0 && Number.isInteger(n) && Math.abs(n % 2) === 1 ? -Math.pow(-a, 1 / n) : Math.pow(a, 1 / n)),
  binomial: (n, k) => factorial(n) / (factorial(k) * factorial(n - k)),
  nCr: (n, k) => factorial(n) / (factorial(k) * factorial(n - k)),
  nPr: (n, k) => factorial(n) / factorial(n - k),
  atan2: Math.atan2,
};
const FNV = { min: Math.min, max: Math.max };
const KNOWN_FNS = new Set([...Object.keys(FN1), ...Object.keys(FN2), ...Object.keys(FNV), "log", "piecewise"]);

// ---------------------------------------------------------------- compiler
const NAN = () => NaN;

// Compile a tree into (env: number[]) => number, where env[i] is the value of names[i].
export function compileEnv(tree, names) {
  return cnum(tree, names.slice());
}

// Compile a tree into (...values) => number.
export function compile(tree, varNames = ["x"]) {
  const c = compileEnv(tree, varNames);
  return (...vals) => c(vals);
}

function cnum(u, names) {
  switch (u.k) {
    case "num": {
      const v = N.toFloat(u.v);
      return () => v;
    }
    case "const": {
      const v = u.name === "pi" ? Math.PI : u.name === "e" ? Math.E : u.name === "oo" ? Infinity : NaN;
      return () => v;
    }
    case "bool": {
      const v = u.v ? 1 : 0;
      return () => v;
    }
    case "sym": {
      const i = names.lastIndexOf(u.name);
      if (i < 0) return NAN;
      return (env) => env[i];
    }
    case "add": {
      const cs = u.args.map((a) => cnum(a, names));
      if (cs.length === 2) { const [a, b] = cs; return (env) => a(env) + b(env); }
      return (env) => { let s = 0; for (const c of cs) s += c(env); return s; };
    }
    case "mul": {
      const cs = u.args.map((a) => cnum(a, names));
      if (cs.length === 2) { const [a, b] = cs; return (env) => a(env) * b(env); }
      return (env) => { let s = 1; for (const c of cs) s *= c(env); return s; };
    }
    case "pow": return cpow(u, names);
    case "fn": return cfn(u, names);
    case "eq": case "rel": {
      const a = cnum(u.args[0], names), b = cnum(u.args[1], names);
      return (env) => a(env) - b(env);
    }
    case "and": case "or": case "not": {
      const c = cbool(u, names);
      return (env) => (c(env) ? 1 : 0);
    }
    case "piecewise": return cpiece(u.args, names);
    case "sum": case "product": return cbig(u, names);
    default: return NAN;
  }
}

function cpow(u, names) {
  const [b, e] = u.args;
  const cb = cnum(b, names);
  if (b === X.E) {
    const ce = cnum(e, names);
    return (env) => Math.exp(ce(env));
  }
  const ev = exactRational(e);
  if (ev) {
    const p = N.toFloat(ev);
    const d = ev.d, n = ev.n;
    if (d === 1n) {
      if (p === 2) return (env) => { const x = cb(env); return x * x; };
      if (p === -1) return (env) => 1 / cb(env);
      return (env) => Math.pow(cb(env), p);
    }
    if (d % 2n === 1n) {
      // odd root of a negative base is real: (-8)^(1/3) = -2, (-8)^(2/3) = 4
      const sgn = n % 2n === 0n ? 1 : -1;
      return (env) => { const x = cb(env); return x < 0 ? sgn * Math.pow(-x, p) : Math.pow(x, p); };
    }
    if (p === 0.5) return (env) => Math.sqrt(cb(env));
    return (env) => Math.pow(cb(env), p);
  }
  const ce = cnum(e, names);
  return (env) => Math.pow(cb(env), ce(env));
}

// Exact rational value of a constant tree built from numbers (e.g. the raw parse of 1/3), else null.
function exactRational(u, depth = 0) {
  if (depth > 20) return null;
  if (u.k === "num") return u.v;
  if (u.k === "add" || u.k === "mul") {
    let acc = u.k === "add" ? N.ZERO : N.ONE;
    for (const a of u.args) {
      const v = exactRational(a, depth + 1);
      if (!v) return null;
      acc = u.k === "add" ? N.add(acc, v) : N.mul(acc, v);
    }
    return acc;
  }
  if (u.k === "pow" && u.args[1].k === "num" && u.args[1].v.d === 1n) {
    const b = exactRational(u.args[0], depth + 1);
    const k = u.args[1].v.n;
    if (!b || k > 64n || k < -64n || (k < 0n && b.n === 0n)) return null;
    return N.pow(b, k);
  }
  return null;
}

function cfn(u, names) {
  const name = u.name;
  if (name === "piecewise") return cpiece(u.args, names);
  const cs = u.args.map((a) => cnum(a, names));
  if (name === "log") {
    if (cs.length === 1) { const [a] = cs; return (env) => Math.log10(a(env)); }
    const [b, a] = cs;
    if (u.args[0].k === "num" && u.args[0].v.n === 10n && u.args[0].v.d === 1n) return (env) => Math.log10(a(env));
    if (u.args[0].k === "num" && u.args[0].v.n === 2n && u.args[0].v.d === 1n) return (env) => Math.log2(a(env));
    return (env) => Math.log(a(env)) / Math.log(b(env));
  }
  if (FN1[name] && cs.length === 1) { const f = FN1[name], [a] = cs; return (env) => f(a(env)); }
  if (FN2[name] && cs.length === 2) { const f = FN2[name], [a, b] = cs; return (env) => f(a(env), b(env)); }
  if (FNV[name] && cs.length >= 1) { const f = FNV[name]; return (env) => f(...cs.map((c) => c(env))); }
  return NAN;
}

function cpiece(args, names) {
  const pairs = [];
  for (let i = 0; i + 1 < args.length; i += 2) pairs.push([cnum(args[i], names), cbool(args[i + 1], names)]);
  if (args.length % 2 === 1) pairs.push([cnum(args[args.length - 1], names), () => true]); // trailing default
  return (env) => {
    for (const [v, c] of pairs) if (c(env)) return v(env);
    return NaN;
  };
}

function cbool(u, names) {
  switch (u.k) {
    case "bool": { const v = !!u.v; return () => v; }
    case "const": return () => false;
    case "sym": if (u.name === "otherwise" || u.name === "true") return () => true; break;
    case "rel": {
      const a = cnum(u.args[0], names), b = cnum(u.args[1], names);
      switch (u.op) {
        case "<": return (env) => a(env) < b(env);
        case "<=": return (env) => a(env) <= b(env);
        case ">": return (env) => a(env) > b(env);
        case ">=": return (env) => a(env) >= b(env);
        case "!=": return (env) => a(env) !== b(env);
      }
      return () => false;
    }
    case "eq": {
      const a = cnum(u.args[0], names), b = cnum(u.args[1], names);
      return (env) => { const p = a(env), q = b(env); return Math.abs(p - q) <= 1e-12 * Math.max(1, Math.abs(p), Math.abs(q)); };
    }
    case "and": { const cs = u.args.map((a) => cbool(a, names)); return (env) => cs.every((c) => c(env)); }
    case "or": { const cs = u.args.map((a) => cbool(a, names)); return (env) => cs.some((c) => c(env)); }
    case "not": { const c = cbool(u.args[0], names); return (env) => !c(env); }
  }
  const c = cnum(u, names);
  return (env) => { const v = c(env); return v !== 0 && !Number.isNaN(v); };
}

function cbig(u, names) {
  const [e, v, lo, hi] = u.args;
  const inner = names.concat(v.name);
  const body = cnum(e, inner), clo = cnum(lo, names), chi = cnum(hi, names);
  const isSum = u.k === "sum";
  return (env) => {
    const a = Math.ceil(clo(env) - 1e-9), b = Math.floor(chi(env) + 1e-9);
    if (!Number.isFinite(a) || !Number.isFinite(b) || b - a > 100000) return NaN;
    const ev = env.slice(0, names.length);
    ev.length = names.length + 1;
    let s = isSum ? 0 : 1;
    for (let k = a; k <= b; k++) { ev[names.length] = k; s = isSum ? s + body(ev) : s * body(ev); }
    return s;
  };
}

// ---------------------------------------------------------------- ticks
export function niceTicks(min, max, approxCount = 8) {
  if (!(max > min) || !Number.isFinite(min) || !Number.isFinite(max)) return { step: 1, ticks: [] };
  const raw = (max - min) / Math.max(1, approxCount);
  const mag = Math.pow(10, Math.floor(Math.log10(raw)));
  const r = raw / mag;
  const step = (r < 1.5 ? 1 : r < 3.5 ? 2 : r < 7.5 ? 5 : 10) * mag;
  const ticks = [];
  const start = Math.ceil(min / step - 1e-9);
  const end = Math.floor(max / step + 1e-9);
  for (let i = start; i <= end && ticks.length < 1000; i++) {
    const t = i * step;
    ticks.push(Math.abs(t) < step * 1e-9 ? 0 : t);
  }
  return { step, ticks };
}

// ---------------------------------------------------------------- 1-D adaptive sampler
// Returns segments (arrays of [x, y]); points are never joined across a discontinuity.
export function sampleFunction(f, xmin, xmax, opts = {}) {
  const maxDepth = opts.maxDepth ?? 10;
  const initial = Math.max(8, opts.initial ?? 200);
  let { ymin, ymax } = opts;
  if (!(ymax > ymin)) {
    const ys = [];
    for (let i = 0; i <= 64; i++) { const y = f(xmin + ((xmax - xmin) * i) / 64); if (Number.isFinite(y)) ys.push(y); }
    ys.sort((a, b) => a - b);
    ymin = ys.length ? ys[Math.floor(ys.length * 0.1)] : -10;
    ymax = ys.length ? ys[Math.floor(ys.length * 0.9)] : 10;
    if (!(ymax - ymin > 1e-9)) { ymin -= 1; ymax += 1; }
  }
  const H = ymax - ymin;
  const tolDev = H * 0.0015;
  const bigJump = H * 0.25;
  const jumpMin = H * 1e-3;
  const hiOff = ymax + H, loOff = ymin - H;

  const segs = [];
  let cur = [];
  const brk = () => { if (cur.length) segs.push(cur); cur = []; };
  const push = (x, y) => { if (Number.isFinite(y)) cur.push([x, y]); else brk(); };

  function refine(x0, y0, x1, y1, d, pdy) {
    const f0 = Number.isFinite(y0), f1 = Number.isFinite(y1);
    if (d >= maxDepth) {
      if (f0 && f1) {
        const dy = Math.abs(y1 - y0);
        // a real jump does not shrink under bisection; a continuous change halves
        if (dy > jumpMin && dy > 0.9 * pdy) brk();
      }
      return;
    }
    const xm = (x0 + x1) / 2;
    if (!f0 && !f1) {
      if (d >= 3) return;
      const ym = f(xm);
      refine(x0, y0, xm, ym, d + 1, Infinity); push(xm, ym); refine(xm, ym, x1, y1, d + 1, Infinity);
      return;
    }
    const ym = f(xm);
    if (!f0 || !f1 || !Number.isFinite(ym)) {
      // locate the edge of the domain / the pole
      refine(x0, y0, xm, ym, d + 1, Infinity); push(xm, ym); refine(xm, ym, x1, y1, d + 1, Infinity);
      return;
    }
    // far off-screen on one side: nothing visible to refine
    if ((y0 > hiOff && y1 > hiOff && ym > hiOff) || (y0 < loOff && y1 < loOff && ym < loOff)) return;
    const dy = Math.abs(y1 - y0);
    const dev = Math.abs(ym - (y0 + y1) / 2);
    if (dev > tolDev || dy > bigJump) {
      refine(x0, y0, xm, ym, d + 1, dy); push(xm, ym); refine(xm, ym, x1, y1, d + 1, dy);
    }
  }

  // split the domain at known poles
  const span = xmax - xmin;
  const eps = span * 1e-9;
  const cuts = [...new Set((opts.poles || []).map(Number))].filter((p) => Number.isFinite(p) && p > xmin && p < xmax).sort((a, b) => a - b);
  const bounds = [xmin];
  for (const p of cuts) bounds.push(p - eps, p + eps);
  bounds.push(xmax);
  for (let k = 0; k + 1 < bounds.length; k += 2) {
    const a = bounds[k], b = bounds[k + 1];
    if (!(b > a)) continue;
    const n = Math.max(2, Math.round((initial * (b - a)) / span));
    let x0 = a, y0 = f(a);
    push(x0, y0);
    for (let i = 1; i <= n; i++) {
      const x1 = i === n ? b : a + ((b - a) * i) / n;
      const y1 = f(x1);
      refine(x0, y0, x1, y1, 0, Infinity);
      push(x1, y1);
      x0 = x1; y0 = y1;
    }
    brk();
  }
  brk();
  return segs;
}

// ---------------------------------------------------------------- parametric / polar
export function sampleParametric(fx, fy, t0, t1, opts = {}) {
  const n = opts.n ?? 1000;
  const maxJump = opts.maxJump ?? Infinity;
  const segs = [];
  let cur = [], prev = null;
  for (let i = 0; i <= n; i++) {
    const t = t0 + ((t1 - t0) * i) / n;
    const x = fx(t), y = fy(t);
    if (!Number.isFinite(x) || !Number.isFinite(y)) { if (cur.length) segs.push(cur); cur = []; prev = null; continue; }
    if (prev && Math.hypot(x - prev[0], y - prev[1]) > maxJump) { if (cur.length) segs.push(cur); cur = []; }
    prev = [x, y];
    cur.push(prev);
  }
  if (cur.length) segs.push(cur);
  return segs;
}
export function samplePolar(fr, th0, th1, opts = {}) {
  return sampleParametric((t) => fr(t) * Math.cos(t), (t) => fr(t) * Math.sin(t), th0, th1, opts);
}

// ---------------------------------------------------------------- marching squares
export function implicitCurve(F, xmin, xmax, ymin, ymax, opts = {}) {
  const nx = Math.max(2, opts.nx ?? 120), ny = Math.max(2, opts.ny ?? 120);
  const refine = opts.refine ?? true;
  const dx = (xmax - xmin) / nx, dy = (ymax - ymin) / ny;
  const V = new Float64Array((nx + 1) * (ny + 1));
  for (let j = 0; j <= ny; j++) for (let i = 0; i <= nx; i++) V[j * (nx + 1) + i] = F(xmin + i * dx, ymin + j * dy);
  const out = [];
  for (let j = 0; j < ny; j++) {
    for (let i = 0; i < nx; i++) {
      const b = j * (nx + 1) + i;
      cell(F, xmin + i * dx, ymin + j * dy, dx, dy, V[b], V[b + 1], V[b + nx + 1], V[b + nx + 2], refine ? 1 : 0, out);
    }
  }
  return out;
}

// v00 bottom-left, v10 bottom-right, v01 top-left, v11 top-right
function cell(F, x0, y0, dx, dy, v00, v10, v01, v11, level, out) {
  if (!(Number.isFinite(v00) && Number.isFinite(v10) && Number.isFinite(v01) && Number.isFinite(v11))) return;
  const s00 = v00 > 0, s10 = v10 > 0, s01 = v01 > 0, s11 = v11 > 0;
  if (s00 === s10 && s00 === s01 && s00 === s11) return;
  if (level > 0) {
    const hx = dx / 2, hy = dy / 2;
    const vb = F(x0 + hx, y0), vl = F(x0, y0 + hy), vc = F(x0 + hx, y0 + hy), vr = F(x0 + dx, y0 + hy), vt = F(x0 + hx, y0 + dy);
    cell(F, x0, y0, hx, hy, v00, vb, vl, vc, level - 1, out);
    cell(F, x0 + hx, y0, hx, hy, vb, v10, vc, vr, level - 1, out);
    cell(F, x0, y0 + hy, hx, hy, vl, vc, v01, vt, level - 1, out);
    cell(F, x0 + hx, y0 + hy, hx, hy, vc, vr, vt, v11, level - 1, out);
    return;
  }
  // crossing on an edge from (xa,ya,va) to (xb,yb,vb); null when absent or caused by a pole
  const edge = (xa, ya, va, xb, yb, vb) => {
    if ((va > 0) === (vb > 0)) return null;
    const t = va / (va - vb);
    const px = xa + (xb - xa) * t, py = ya + (yb - ya) * t;
    const fp = F(px, py);
    if (!Number.isFinite(fp) || Math.abs(fp) > Math.max(Math.abs(va), Math.abs(vb))) return null;
    return [px, py];
  };
  const x1 = x0 + dx, y1 = y0 + dy;
  const eb = edge(x0, y0, v00, x1, y0, v10);
  const er = edge(x1, y0, v10, x1, y1, v11);
  const et = edge(x0, y1, v01, x1, y1, v11);
  const el = edge(x0, y0, v00, x0, y1, v01);
  const pts = [eb, er, et, el].filter(Boolean);
  if (pts.length === 2) { out.push([pts[0][0], pts[0][1], pts[1][0], pts[1][1]]); return; }
  if (pts.length === 4) {
    const vc = F(x0 + dx / 2, y0 + dy / 2);
    if ((vc > 0) === s00) { // bottom-left and top-right joined through the centre
      out.push([eb[0], eb[1], er[0], er[1]], [et[0], et[1], el[0], el[1]]);
    } else {
      out.push([eb[0], eb[1], el[0], el[1]], [er[0], er[1], et[0], et[1]]);
    }
  }
}

// ---------------------------------------------------------------- inequality regions
// Cell (i, j) (j counted upward from ymin) is 1 when G(cell centre) op 0 holds.
export function inequalityGrid(G, op, xmin, xmax, ymin, ymax, nx, ny) {
  const m = new Uint8Array(nx * ny);
  const dx = (xmax - xmin) / nx, dy = (ymax - ymin) / ny;
  const test = OPS[op] || OPS[">"];
  for (let j = 0; j < ny; j++) {
    const y = ymin + (j + 0.5) * dy;
    for (let i = 0; i < nx; i++) {
      const v = G(xmin + (i + 0.5) * dx, y);
      m[j * nx + i] = Number.isFinite(v) && test(v) ? 1 : 0;
    }
  }
  return m;
}
const OPS = {
  "<": (v) => v < 0, "<=": (v) => v <= 0, ">": (v) => v > 0, ">=": (v) => v >= 0,
  "!=": (v) => v !== 0, "=": (v) => Math.abs(v) < 1e-9,
};

// ---------------------------------------------------------------- classification
const PLOT_VARS = new Set(["x", "y", "t", "theta", "r"]);
const COMPILABLE = new Set(["num", "sym", "const", "add", "mul", "pow", "fn", "piecewise", "bool", "eq", "rel", "and", "or", "not", "sum", "product"]);

function unsupported(u) {
  if (!COMPILABLE.has(u.k)) return u.k;
  if (u.k === "fn" && !KNOWN_FNS.has(u.name)) return u.name;
  for (const a of u.args) { const r = unsupported(a); if (r) return r; }
  return null;
}
const free = (u) => [...X.freeSymbols(u)];
const paramsOf = (u, exclude) => free(u).filter((n) => !exclude.includes(n) && !PLOT_VARS.has(n)).sort();
const isNumeric = (u) => X.freeSymbols(u).size === 0 && !unsupported(u);

export function classifyPlot(tree) {
  if (!tree || typeof tree !== "object" || !tree.k) return { type: "none", reason: "nothing to plot", params: [] };
  switch (tree.k) {
    case "system": return multi(tree.args.map(classifyPlot));
    case "set": case "tuple": case "vector": {
      const pts = pointsOf(tree);
      if (pts) return { type: "points", points: pts, params: [] };
      if ((tree.k === "tuple" || tree.k === "vector") && tree.args.length === 2) return parametric(tree.args[0], tree.args[1]);
      if (tree.k === "set") return multi(tree.args.map(classifyPlot));
      return { type: "none", reason: "cannot plot a " + tree.k, params: [] };
    }
    case "fndef": {
      const ps = tree.args[0].args;
      if (ps.length !== 1 || ps[0].k !== "sym") return { type: "none", reason: "only one-variable functions are plotted", params: [] };
      return fnItem(tree.args[1], ps[0].name);
    }
  }
  const bad = unsupported(tree);
  if (bad) return { type: "none", reason: `cannot evaluate ${bad} numerically`, params: [] };
  if (tree.k === "eq") return classifyEq(tree);
  if (tree.k === "rel") return ineq([{ G: X.sub(tree.args[0], tree.args[1]), op: tree.op }], "and", tree);
  if (tree.k === "and" || tree.k === "or") {
    if (tree.args.every((a) => a.k === "rel")) return ineq(tree.args.map((a) => ({ G: X.sub(a.args[0], a.args[1]), op: a.op })), tree.k, tree);
    return multi(tree.args.map(classifyPlot));
  }
  if (tree.k === "not" || tree.k === "bool") return { type: "none", reason: "nothing to plot", params: [] };
  return fnItem(tree);
}

function multi(items) {
  const ok = items.filter((i) => i.type !== "none");
  if (!ok.length) return items[0] || { type: "none", reason: "nothing to plot", params: [] };
  if (ok.length === 1) return ok[0];
  const params = [...new Set(ok.flatMap((i) => i.params))].sort();
  return { type: "multi", items: ok, params };
}
function pointsOf(u) {
  const pt = (p) => ((p.k === "tuple" || p.k === "vector") && p.args.length === 2 && p.args.every(isNumeric)
    ? [compile(p.args[0], [])(), compile(p.args[1], [])()] : null);
  if (u.k === "set" || (u.k === "tuple" && u.args.every((a) => a.k === "tuple" || a.k === "vector"))) {
    const ps = u.args.map(pt);
    return ps.length && ps.every(Boolean) ? ps : null;
  }
  const p = pt(u);
  return p ? [p] : null;
}
function fnItem(expr, forced) {
  const fs = free(expr);
  let v = forced || "x";
  if (!forced && !fs.includes("x")) {
    const others = fs.filter((n) => n !== "y");
    if (others.length === 1) v = others[0];
    else if (fs.includes("t")) v = "t";
    else if (fs.includes("theta")) v = "theta";
  }
  return { type: "function", expr, var: v, params: fs.filter((n) => n !== v && !PLOT_VARS.has(n)).sort() };
}
function parametric(ex, ey) {
  const fs = [...new Set([...free(ex), ...free(ey)])];
  let v = "t";
  if (!fs.includes("t")) {
    const cand = fs.filter((n) => n !== "x" && n !== "y");
    v = cand.length === 1 ? cand[0] : fs.includes("theta") ? "theta" : "t";
  }
  return { type: "parametric", x: ex, y: ey, var: v, params: fs.filter((n) => n !== v && !PLOT_VARS.has(n)).sort() };
}
function classifyEq(u) {
  const [l, r] = u.args;
  const hasY = (w) => X.hasSym(w, "y");
  if (X.isSym(l, "y") && !hasY(r)) return fnItem(r, free(r).includes("x") || free(r).length !== 1 ? "x" : free(r)[0]);
  if (X.isSym(r, "y") && !hasY(l)) return fnItem(l, free(l).includes("x") || free(l).length !== 1 ? "x" : free(l)[0]);
  if (X.isSym(l, "r") && !X.hasSym(r, "r")) return { type: "polar", expr: r, var: "theta", params: paramsOf(r, ["theta"]) };
  if (X.isSym(r, "r") && !X.hasSym(l, "r")) return { type: "polar", expr: l, var: "theta", params: paramsOf(l, ["theta"]) };
  const fs = free(u);
  if (fs.includes("x") && fs.includes("y")) return { type: "implicit", G: X.sub(l, r), params: paramsOf(u, ["x", "y"]) };
  if (fs.includes("y") && !fs.includes("x")) return { type: "implicit", G: X.sub(l, r), params: paramsOf(u, ["x", "y"]) };
  if (!fs.length) return { type: "none", reason: "no variables to plot", params: [] };
  // one-variable equation: plot both sides; the solutions are where they meet
  const main = fs.includes("x") ? "x" : fs.length === 1 ? fs[0] : fs.sort()[0];
  return multi([fnItem(l, main), fnItem(r, main)]);
}
function ineq(conds, join, tree) {
  return { type: "inequality", conds, join, params: paramsOf(tree, ["x", "y"]) };
}

// ---------------------------------------------------------------- DOM grapher
const DEFAULT_COLORS = { "--plot-1": "#0a84c6", "--plot-2": "#d9480f", "--plot-3": "#2b8a3e", "--plot-4": "#7048e8", "--grid": "rgba(128,128,128,.18)", "--axis": "rgba(128,128,128,.7)", "--txt": "#222", "--mut": "#666", "--bg": "#fff" };
const SVGNS = "http://www.w3.org/2000/svg";
const ICONS = {
  zoomIn: "M10.5 4a6.5 6.5 0 1 1 0 13 6.5 6.5 0 0 1 0-13zM15.3 15.3 20 20M10.5 7.5v6M7.5 10.5h6",
  zoomOut: "M10.5 4a6.5 6.5 0 1 1 0 13 6.5 6.5 0 0 1 0-13zM15.3 15.3 20 20M7.5 10.5h6",
  reset: "M4 12a8 8 0 1 0 2.4-5.7M4 4v4.5h4.5M12 9v6M9 12h6",
};
let GRAPH_SEQ = 0;

function fmtNum(v, step) {
  if (!Number.isFinite(v)) return String(v);
  if (v === 0) return "0";
  const a = Math.abs(v);
  if (a >= 1e6 || a < 1e-4) return v.toExponential(2).replace("e+", "e");
  if (step) {
    const dec = Math.max(0, Math.min(10, -Math.floor(Math.log10(step) + 1e-9)));
    return v.toFixed(dec);
  }
  return String(+v.toPrecision(6));
}

// Liang-Barsky clip of segment p->q to a box; returns [x0,y0,x1,y1] or null
function clip(x0, y0, x1, y1, bx0, by0, bx1, by1) {
  let t0 = 0, t1 = 1;
  const dx = x1 - x0, dy = y1 - y0;
  const p = [-dx, dx, -dy, dy], q = [x0 - bx0, bx1 - x0, y0 - by0, by1 - y0];
  for (let i = 0; i < 4; i++) {
    if (p[i] === 0) { if (q[i] < 0) return null; continue; }
    const r = q[i] / p[i];
    if (p[i] < 0) { if (r > t1) return null; if (r > t0) t0 = r; }
    else { if (r < t0) return null; if (r < t1) t1 = r; }
  }
  return [x0 + t0 * dx, y0 + t0 * dy, x0 + t1 * dx, y0 + t1 * dy];
}

export function createGraph(container, opts = {}) {
  const doc = container.ownerDocument;
  const win = doc.defaultView;
  const uid = ++GRAPH_SEQ;
  const h = (tag, cls, attrs = {}) => {
    const e = doc.createElement(tag);
    if (cls) e.className = cls;
    for (const [k, v] of Object.entries(attrs)) e.setAttribute(k, v);
    return e;
  };
  const icon = (d) => {
    const s = doc.createElementNS(SVGNS, "svg");
    s.setAttribute("viewBox", "0 0 24 24"); s.setAttribute("width", "18"); s.setAttribute("height", "18");
    s.setAttribute("aria-hidden", "true"); s.setAttribute("focusable", "false");
    const p = doc.createElementNS(SVGNS, "path");
    p.setAttribute("d", d); p.setAttribute("fill", "none"); p.setAttribute("stroke", "currentColor");
    p.setAttribute("stroke-width", "1.8"); p.setAttribute("stroke-linecap", "round"); p.setAttribute("stroke-linejoin", "round");
    s.appendChild(p);
    return s;
  };

  const root = h("div", "qg");
  const toolbar = h("div", "qg-toolbar", { role: "toolbar", "aria-label": "Graph controls" });
  const mkBtn = (label, d, fn) => {
    const b = h("button", "qg-btn", { type: "button", "aria-label": label, title: label });
    b.appendChild(icon(d));
    b.addEventListener("click", fn);
    toolbar.appendChild(b);
    return b;
  };
  mkBtn("Zoom in", ICONS.zoomIn, () => zoom(1 / 1.5));
  mkBtn("Zoom out", ICONS.zoomOut, () => zoom(1.5));
  mkBtn("Reset view", ICONS.reset, () => resetView());
  const wrap = h("div", "qg-canvas-wrap");
  wrap.style.position = "relative";
  wrap.style.width = "100%";
  wrap.style.height = "var(--qg-height, 320px)";
  wrap.style.touchAction = "none";
  const canvas = h("canvas", "qg-canvas", { tabindex: "0", role: "img", "aria-label": "Empty graph" });
  canvas.style.display = "block";
  canvas.style.width = "100%";
  canvas.style.height = "100%";
  wrap.appendChild(canvas);
  const legend = h("ul", "qg-legend", { "aria-label": "Legend" });
  const readout = h("div", "qg-readout", { "aria-live": "off" });
  readout.textContent = "Drag to pan, scroll or pinch to zoom. Keys: arrows pan, + and - zoom, 0 resets.";
  const sliders = h("div", "qg-sliders");
  sliders.hidden = true;
  root.append(toolbar, wrap, legend, readout, sliders);
  container.appendChild(root);

  const ctx = canvas.getContext("2d");
  let cssW = 0, cssH = 0, dpr = 1, raf = 0, destroyed = false;
  let view = { xmin: -10, xmax: 10, ymin: -10, ymax: 10 };
  let home = { ...view };
  let items = [];       // { kind, color, label, ...compiled evaluators }
  let marks = [], asymptotes = [], poles = [];
  let params = [];      // names
  const pv = [];        // current parameter values (shared by every evaluator)
  let hover = null;

  function colors() {
    const cs = win.getComputedStyle(container);
    const out = {};
    for (const k of Object.keys(DEFAULT_COLORS)) out[k] = cs.getPropertyValue(k).trim() || DEFAULT_COLORS[k];
    out.font = cs.fontFamily || "system-ui, sans-serif";
    return out;
  }
  const schedule = () => { if (!raf && !destroyed) raf = win.requestAnimationFrame(render); };

  // evaluator over plot variables with the shared parameter vector appended
  function evaluator(tree, vars) {
    const c = compileEnv(tree, vars.concat(params));
    const env = new Array(vars.length + params.length);
    const n = vars.length;
    if (n === 1) return (a) => { env[0] = a; for (let i = 0; i < params.length; i++) env[n + i] = pv[i]; return c(env); };
    return (a, b) => { env[0] = a; env[1] = b; for (let i = 0; i < params.length; i++) env[n + i] = pv[i]; return c(env); };
  }
  const exprLabel = (t) => { try { return toText(t); } catch (_) { return "expression"; } };

  function build(cls, colorIdx, src) {
    switch (cls.type) {
      case "function": {
        const label = (cls.var === "x" ? "y = " : `y(${cls.var}) = `) + exprLabel(cls.expr);
        return [{ kind: "function", colorIdx, label, f: evaluator(cls.expr, [cls.var]) }];
      }
      case "implicit": return [{ kind: "implicit", colorIdx, label: exprLabel(src), F: evaluator(cls.G, ["x", "y"]) }];
      case "inequality": return [{ kind: "inequality", colorIdx, label: exprLabel(src), join: cls.join, conds: cls.conds.map((c) => ({ op: c.op, G: evaluator(c.G, ["x", "y"]) })) }];
      case "polar": {
        const trigOnly = onlyInsideTrig(cls.expr, "theta");
        return [{ kind: "curve", colorIdx, label: "r = " + exprLabel(cls.expr), t0: 0, t1: trigOnly ? 2 * Math.PI : 6 * Math.PI, polar: true, fr: evaluator(cls.expr, ["theta"]) }];
      }
      case "parametric": {
        const trig = onlyInsideTrig(cls.x, cls.var) && onlyInsideTrig(cls.y, cls.var);
        return [{ kind: "curve", colorIdx, label: `(${exprLabel(cls.x)}, ${exprLabel(cls.y)})`, t0: trig ? 0 : -10, t1: trig ? 2 * Math.PI : 10, fx: evaluator(cls.x, [cls.var]), fy: evaluator(cls.y, [cls.var]) }];
      }
      case "points": return [{ kind: "points", colorIdx, label: cls.points.map((p) => `(${fmtNum(p[0])}, ${fmtNum(p[1])})`).join(", "), points: cls.points }];
      case "multi": {
        const out = [];
        cls.items.forEach((it, k) => out.push(...build(it, colorIdx + k, it.expr || it.G || src)));
        return out;
      }
      default: return [];
    }
  }

  function set(data = {}) {
    const exprs = (data.exprs || []).filter(Boolean);
    const classes = exprs.map((t) => ({ t, c: classifyPlot(t) }));
    params = [...new Set(classes.flatMap(({ c }) => c.params || []))].sort();
    const prev = new Map(sliders._vals || []);
    pv.length = 0;
    params.forEach((p) => pv.push(prev.has(p) ? prev.get(p) : 1));
    items = [];
    let idx = 0;
    for (const { t, c } of classes) {
      const built = build(c, idx, t);
      items.push(...built);
      idx += Math.max(1, built.length);
    }
    const none = classes.filter(({ c }) => c.type === "none").map(({ c }) => c.reason);
    marks = (data.marks || []).map((m) => ({ ...m, x: Number(m.x), y: m.y == null ? NaN : Number(m.y) })).filter((m) => Number.isFinite(m.x));
    asymptotes = (data.asymptotes || []).map((a) => (typeof a === "number" ? { x: a } : a)).filter((a) => a && (Number.isFinite(+a.x) || Number.isFinite(+a.y)));
    poles = [...(data.poles || []).map(Number), ...asymptotes.filter((a) => a.x != null).map((a) => +a.x)].filter(Number.isFinite);
    buildSliders();
    buildLegend();
    home = fitView();
    view = { ...home };
    if (opts.onStatus) opts.onStatus(items.length ? "ok" : none[0] || "nothing to plot");
    updateAria();
    schedule();
  }

  function buildSliders() {
    sliders.textContent = "";
    sliders.hidden = !params.length;
    sliders._vals = new Map(params.map((p, i) => [p, pv[i]]));
    params.forEach((p, i) => {
      const id = `qg${uid}-p-${p}`;
      const row = h("div", "qg-slider");
      const lab = h("label", "", { for: id });
      lab.textContent = p;
      const inp = h("input", "", { id, type: "range", min: "-10", max: "10", step: "0.1", value: String(pv[i]) });
      const out = h("output", "", { for: id });
      out.textContent = fmtNum(pv[i]);
      inp.addEventListener("input", () => {
        pv[i] = Number(inp.value);
        sliders._vals.set(p, pv[i]);
        out.textContent = fmtNum(pv[i]);
        updateAria();
        schedule();
      });
      row.append(lab, inp, out);
      sliders.appendChild(row);
    });
  }
  function buildLegend() {
    legend.textContent = "";
    const c = colors();
    for (const it of items) {
      const li = h("li");
      const sw = h("span", "qg-swatch", { "aria-hidden": "true" });
      sw.style.cssText = `display:inline-block;width:14px;height:3px;border-radius:2px;vertical-align:middle;margin-right:6px;background:${c["--plot-" + ((it.colorIdx % 4) + 1)]}`;
      li.append(sw, doc.createTextNode(it.label));
      legend.appendChild(li);
    }
    legend.hidden = !items.length;
  }

  function fitView() {
    let xmin = -10, xmax = 10;
    const mx = marks.map((m) => m.x);
    if (mx.length) {
      const lo = Math.min(...mx), hi = Math.max(...mx);
      if (lo < xmin + 1 || hi > xmax - 1) {
        const pad = Math.max(1, (hi - lo) * 0.25);
        xmin = Math.min(xmin, lo - pad); xmax = Math.max(xmax, hi + pad);
      }
    }
    const fns = items.filter((i) => i.kind === "function");
    const aspect = cssH && cssW ? cssH / cssW : 0.6;
    if (!fns.length) {
      const pts = items.filter((i) => i.kind === "points").flatMap((i) => i.points);
      const all = pts.concat(marks.filter((m) => Number.isFinite(m.y)).map((m) => [m.x, m.y]));
      if (all.length) {
        const xs = all.map((p) => p[0]), ys = all.map((p) => p[1]);
        const cx = (Math.min(...xs) + Math.max(...xs)) / 2, cy = (Math.min(...ys) + Math.max(...ys)) / 2;
        const half = Math.max(5, (Math.max(...xs) - Math.min(...xs)) * 0.75, (Math.max(...ys) - Math.min(...ys)) * 0.75 / aspect);
        return { xmin: cx - half, xmax: cx + half, ymin: cy - half * aspect, ymax: cy + half * aspect };
      }
      const half = (xmax - xmin) / 2 * aspect;
      return { xmin, xmax, ymin: -half, ymax: half };
    }
    const ys = [];
    for (const it of fns) for (let i = 0; i <= 200; i++) { const y = it.f(xmin + ((xmax - xmin) * i) / 200); if (Number.isFinite(y)) ys.push(y); }
    for (const m of marks) if (Number.isFinite(m.y)) ys.push(m.y);
    if (!ys.length) return { xmin, xmax, ymin: -10, ymax: 10 };
    ys.sort((a, b) => a - b);
    let lo = ys[Math.floor(ys.length * 0.05)], hi = ys[Math.floor(ys.length * 0.95)];
    for (const m of marks) if (Number.isFinite(m.y)) { lo = Math.min(lo, m.y); hi = Math.max(hi, m.y); }
    if (lo > 0 && lo < (hi - lo) * 0.5) lo = 0;
    if (hi < 0 && -hi < (hi - lo) * 0.5) hi = 0;
    let span = hi - lo;
    if (!(span > 1e-9)) { span = Math.max(2, Math.abs(lo) * 0.5); lo -= span / 2; hi += span / 2; }
    span = Math.min(span, 2e6);
    const mid = Math.max(-1e6, Math.min(1e6, (lo + hi) / 2));
    return { xmin, xmax, ymin: mid - span * 0.6, ymax: mid + span * 0.6 };
  }

  function resetView() { view = { ...home }; updateAria(); schedule(); }
  function zoom(factor, cx, cy) {
    const px = cx ?? (view.xmin + view.xmax) / 2, py = cy ?? (view.ymin + view.ymax) / 2;
    const nw = (view.xmax - view.xmin) * factor, nh = (view.ymax - view.ymin) * factor;
    if (nw < 1e-9 || nw > 1e9 || nh < 1e-9 || nh > 1e9) return;
    view = {
      xmin: px - (px - view.xmin) * factor, xmax: px + (view.xmax - px) * factor,
      ymin: py - (py - view.ymin) * factor, ymax: py + (view.ymax - py) * factor,
    };
    updateAria();
    schedule();
  }
  function pan(dx, dy) {
    view = { xmin: view.xmin + dx, xmax: view.xmax + dx, ymin: view.ymin + dy, ymax: view.ymax + dy };
    schedule();
  }

  function summary() {
    if (!items.length) return "Empty graph";
    const parts = [`Graph of ${items.map((i) => i.label).join("; ")}`];
    if (params.length) parts.push(`parameters ${params.map((p, i) => `${p} = ${fmtNum(pv[i])}`).join(", ")}`);
    if (marks.length) parts.push(`marked points: ${marks.slice(0, 12).map((m) => (m.label ? m.label : `(${fmtNum(m.x)}, ${fmtNum(m.y)})`) + (m.kind ? ` (${m.kind})` : "")).join("; ")}`);
    if (asymptotes.length) parts.push(`asymptotes: ${asymptotes.map((a) => (a.x != null ? `x = ${fmtNum(+a.x)}` : `y = ${fmtNum(+a.y)}`)).join(", ")}`);
    parts.push(`view x from ${fmtNum(view.xmin)} to ${fmtNum(view.xmax)}, y from ${fmtNum(view.ymin)} to ${fmtNum(view.ymax)}`);
    return parts.join(". ") + ".";
  }
  let ariaTimer = 0;
  function updateAria() {
    win.clearTimeout(ariaTimer);
    ariaTimer = win.setTimeout(() => canvas.setAttribute("aria-label", summary()), 150);
  }

  // ------------------------------------------------ render
  function render() {
    raf = 0;
    if (destroyed || !cssW || !cssH) return;
    const w = cssW, hh = cssH;
    const c = colors();
    const { xmin, xmax, ymin, ymax } = view;
    const sx = w / (xmax - xmin), sy = hh / (ymax - ymin);
    const PX = (x) => (x - xmin) * sx, PY = (y) => hh - (y - ymin) * sy;
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, w, hh);
    ctx.lineJoin = "round"; ctx.lineCap = "round";

    // grid
    const tx = niceTicks(xmin, xmax, Math.max(2, Math.round(w / 90)));
    const ty = niceTicks(ymin, ymax, Math.max(2, Math.round(hh / 60)));
    ctx.strokeStyle = c["--grid"]; ctx.lineWidth = 1;
    ctx.beginPath();
    for (const t of tx.ticks) { const p = Math.round(PX(t)) + 0.5; ctx.moveTo(p, 0); ctx.lineTo(p, hh); }
    for (const t of ty.ticks) { const p = Math.round(PY(t)) + 0.5; ctx.moveTo(0, p); ctx.lineTo(w, p); }
    ctx.stroke();
    // axes
    ctx.strokeStyle = c["--axis"]; ctx.lineWidth = 1.25;
    ctx.beginPath();
    const ax = PY(0), ay = PX(0);
    if (ax >= 0 && ax <= hh) { ctx.moveTo(0, Math.round(ax) + 0.5); ctx.lineTo(w, Math.round(ax) + 0.5); }
    if (ay >= 0 && ay <= w) { ctx.moveTo(Math.round(ay) + 0.5, 0); ctx.lineTo(Math.round(ay) + 0.5, hh); }
    ctx.stroke();
    // tick labels
    ctx.fillStyle = c["--mut"]; ctx.font = `11px ${c.font}`;
    const lx = Math.min(hh - 4, Math.max(14, ax + 14));
    ctx.textAlign = "center"; ctx.textBaseline = "alphabetic";
    for (const t of tx.ticks) {
      if (t === 0) continue;
      const s = fmtNum(t, tx.step), half = ctx.measureText(s).width / 2, px = PX(t);
      if (px - half < 2 || px + half > w - 2) continue; // never draw clipped labels at the edges
      ctx.fillText(s, px, lx);
    }
    const ly = Math.min(w - 4, Math.max(40, ay - 5));
    ctx.textAlign = "right"; ctx.textBaseline = "middle";
    for (const t of ty.ticks) { const py = PY(t); if (t !== 0 && py > 7 && py < hh - 7) ctx.fillText(fmtNum(t, ty.step), ly, py); }

    const col = (it) => c["--plot-" + ((it.colorIdx % 4) + 1)];
    // extended box for clipping (keeps lines reaching the edges)
    const ex = (xmax - xmin), ey = (ymax - ymin);
    const box = [xmin - ex, ymin - ey, xmax + ex, ymax + ey];
    const drawSegs = (segs) => {
      ctx.beginPath();
      for (const s of segs) {
        let last = null;
        for (let i = 1; i < s.length; i++) {
          const r = clip(s[i - 1][0], s[i - 1][1], s[i][0], s[i][1], ...box);
          if (!r) { last = null; continue; }
          const a0 = PX(r[0]), b0 = PY(r[1]), a1 = PX(r[2]), b1 = PY(r[3]);
          if (!last || Math.abs(last[0] - a0) > 0.01 || Math.abs(last[1] - b0) > 0.01) ctx.moveTo(a0, b0);
          ctx.lineTo(a1, b1);
          last = [a1, b1];
        }
      }
      ctx.stroke();
    };
    const drawLines = (lines) => {
      ctx.beginPath();
      for (const l of lines) { ctx.moveTo(PX(l[0]), PY(l[1])); ctx.lineTo(PX(l[2]), PY(l[3])); }
      ctx.stroke();
    };
    const gx = Math.max(20, Math.min(180, Math.round(w / 5))), gy = Math.max(20, Math.min(180, Math.round(hh / 5)));

    for (const it of items) {
      ctx.strokeStyle = col(it); ctx.fillStyle = col(it); ctx.lineWidth = 2; ctx.setLineDash([]);
      if (it.kind === "inequality") {
        const nx = Math.max(10, Math.round(w / 4)), ny = Math.max(10, Math.round(hh / 4));
        const grids = it.conds.map((cd) => inequalityGrid(cd.G, cd.op, xmin, xmax, ymin, ymax, nx, ny));
        ctx.globalAlpha = 0.18;
        const cw = w / nx, ch = hh / ny;
        for (let j = 0; j < ny; j++) {
          let run = -1;
          for (let i = 0; i <= nx; i++) {
            let on = false;
            if (i < nx) {
              const k = j * nx + i;
              on = it.join === "or" ? grids.some((g) => g[k]) : grids.every((g) => g[k]);
            }
            if (on && run < 0) run = i;
            else if (!on && run >= 0) { ctx.fillRect(run * cw, hh - (j + 1) * ch, (i - run) * cw + 0.5, ch + 0.5); run = -1; }
          }
        }
        ctx.globalAlpha = 1;
        for (const cd of it.conds) {
          ctx.setLineDash(cd.op === "<" || cd.op === ">" || cd.op === "!=" ? [6, 5] : []);
          drawLines(implicitCurve(cd.G, xmin, xmax, ymin, ymax, { nx: gx, ny: gy, refine: true }));
        }
        ctx.setLineDash([]);
      } else if (it.kind === "implicit") {
        drawLines(implicitCurve(it.F, xmin, xmax, ymin, ymax, { nx: gx, ny: gy, refine: true }));
      } else if (it.kind === "function") {
        drawSegs(sampleFunction(it.f, xmin, xmax, { ymin, ymax, poles, initial: Math.max(100, Math.min(600, Math.round(w / 2))) }));
      } else if (it.kind === "curve") {
        const fx = it.polar ? (t) => it.fr(t) * Math.cos(t) : it.fx;
        const fy = it.polar ? (t) => it.fr(t) * Math.sin(t) : it.fy;
        drawSegs(sampleParametric(fx, fy, it.t0, it.t1, { n: 2000, maxJump: Math.hypot(ex, ey) * 0.5 }));
      } else if (it.kind === "points") {
        for (const p of it.points) { ctx.beginPath(); ctx.arc(PX(p[0]), PY(p[1]), 4, 0, Math.PI * 2); ctx.fill(); }
      }
    }

    // asymptotes
    ctx.strokeStyle = c["--mut"]; ctx.lineWidth = 1.25; ctx.setLineDash([5, 5]);
    ctx.beginPath();
    for (const a of asymptotes) {
      if (a.x != null) { const p = PX(+a.x); ctx.moveTo(p, 0); ctx.lineTo(p, hh); }
      else { const p = PY(+a.y); ctx.moveTo(0, p); ctx.lineTo(w, p); }
    }
    ctx.stroke();
    ctx.setLineDash([]);

    // marks
    const firstFn = items.find((i) => i.kind === "function");
    ctx.font = `12px ${c.font}`; ctx.textAlign = "left"; ctx.textBaseline = "bottom";
    for (const m of marks.slice(0, 40)) {
      const y = Number.isFinite(m.y) ? m.y : firstFn ? firstFn.f(m.x) : 0;
      if (!Number.isFinite(y)) continue;
      const px = PX(m.x), py = PY(y);
      if (px < -10 || px > w + 10 || py < -10 || py > hh + 10) continue;
      ctx.beginPath(); ctx.arc(px, py, 4.5, 0, Math.PI * 2);
      ctx.fillStyle = c["--bg"]; ctx.fill();
      ctx.lineWidth = 2; ctx.strokeStyle = m.kind === "extremum" || m.kind === "max" || m.kind === "min" ? c["--plot-2"] : c["--txt"]; ctx.stroke();
      if (m.label) {
        const tw = ctx.measureText(m.label).width;
        let tx0 = px + 7, ty0 = py - 6;
        if (tx0 + tw > w - 2) tx0 = px - 7 - tw;
        if (ty0 - 14 < 0) ty0 = py + 20;
        ctx.lineWidth = 3; ctx.strokeStyle = c["--bg"]; ctx.strokeText(m.label, tx0, ty0);
        ctx.fillStyle = c["--txt"]; ctx.fillText(m.label, tx0, ty0);
      }
    }

    // crosshair
    if (hover) {
      ctx.strokeStyle = c["--axis"]; ctx.lineWidth = 1; ctx.setLineDash([2, 3]);
      ctx.beginPath();
      ctx.moveTo(hover.px + 0.5, 0); ctx.lineTo(hover.px + 0.5, hh);
      ctx.moveTo(0, hover.py + 0.5); ctx.lineTo(w, hover.py + 0.5);
      ctx.stroke(); ctx.setLineDash([]);
      if (firstFn) {
        const fy = firstFn.f(hover.x);
        if (Number.isFinite(fy)) {
          ctx.beginPath(); ctx.arc(PX(hover.x), PY(fy), 3.5, 0, Math.PI * 2);
          ctx.fillStyle = col(firstFn); ctx.fill();
        }
      }
    }
  }

  // ------------------------------------------------ interaction
  const toData = (px, py) => ({
    x: view.xmin + (px / cssW) * (view.xmax - view.xmin),
    y: view.ymax - (py / cssH) * (view.ymax - view.ymin),
  });
  const localPt = (e) => { const r = canvas.getBoundingClientRect(); return [e.clientX - r.left, e.clientY - r.top]; };
  const pointers = new Map();
  let lastPinch = null;

  function setHover(px, py) {
    const d = toData(px, py);
    hover = { px, py, x: d.x, y: d.y };
    const firstFn = items.find((i) => i.kind === "function");
    let s = `x = ${fmtNum(d.x)}, y = ${fmtNum(d.y)}`;
    if (firstFn) { const fy = firstFn.f(d.x); s += `; ${firstFn.label.split(" = ")[0]} at x: ${Number.isFinite(fy) ? fmtNum(fy) : "undefined"}`; }
    readout.textContent = s;
    schedule();
  }
  const onDown = (e) => {
    canvas.setPointerCapture?.(e.pointerId);
    pointers.set(e.pointerId, localPt(e));
    lastPinch = null;
  };
  const onMove = (e) => {
    const p = localPt(e);
    if (!pointers.has(e.pointerId)) { if (e.pointerType === "mouse") setHover(p[0], p[1]); return; }
    const prev = pointers.get(e.pointerId);
    pointers.set(e.pointerId, p);
    if (pointers.size === 1) {
      const dx = ((prev[0] - p[0]) / cssW) * (view.xmax - view.xmin);
      const dy = ((p[1] - prev[1]) / cssH) * (view.ymax - view.ymin);
      hover = null;
      pan(dx, dy);
    } else if (pointers.size === 2) {
      const [a, b] = [...pointers.values()];
      const dist = Math.hypot(a[0] - b[0], a[1] - b[1]);
      const mid = [(a[0] + b[0]) / 2, (a[1] + b[1]) / 2];
      if (lastPinch && dist > 0) {
        const m0 = toData(...lastPinch.mid);
        const dx = ((lastPinch.mid[0] - mid[0]) / cssW) * (view.xmax - view.xmin);
        const dy = ((mid[1] - lastPinch.mid[1]) / cssH) * (view.ymax - view.ymin);
        zoom(lastPinch.dist / dist, m0.x, m0.y);
        pan(dx, dy);
      }
      lastPinch = { dist, mid };
    }
  };
  const onUp = (e) => {
    pointers.delete(e.pointerId);
    lastPinch = null;
    if (!pointers.size) updateAria();
  };
  const onLeave = () => { if (!pointers.size) { hover = null; schedule(); } };
  const onWheel = (e) => {
    e.preventDefault();
    const [px, py] = localPt(e);
    const d = toData(px, py);
    const dy = e.deltaMode === 1 ? e.deltaY * 16 : e.deltaY;
    zoom(Math.exp(Math.max(-1, Math.min(1, dy * 0.0015))), d.x, d.y);
  };
  const onKey = (e) => {
    const wx = (view.xmax - view.xmin) * 0.1, wy = (view.ymax - view.ymin) * 0.1;
    let handled = true;
    switch (e.key) {
      case "ArrowLeft": pan(-wx, 0); break;
      case "ArrowRight": pan(wx, 0); break;
      case "ArrowUp": pan(0, wy); break;
      case "ArrowDown": pan(0, -wy); break;
      case "+": case "=": zoom(1 / 1.5); break;
      case "-": case "_": zoom(1.5); break;
      case "0": resetView(); break;
      default: handled = false;
    }
    if (handled) {
      e.preventDefault();
      readout.textContent = `View x from ${fmtNum(view.xmin)} to ${fmtNum(view.xmax)}, y from ${fmtNum(view.ymin)} to ${fmtNum(view.ymax)}`;
      updateAria();
    }
  };
  canvas.addEventListener("pointerdown", onDown);
  canvas.addEventListener("pointermove", onMove);
  canvas.addEventListener("pointerup", onUp);
  canvas.addEventListener("pointercancel", onUp);
  canvas.addEventListener("pointerleave", onLeave);
  canvas.addEventListener("wheel", onWheel, { passive: false });
  canvas.addEventListener("keydown", onKey);

  function resize() {
    const r = wrap.getBoundingClientRect();
    const nw = Math.max(1, Math.round(r.width)), nh = Math.max(1, Math.round(r.height));
    dpr = Math.max(1, Math.min(3, win.devicePixelRatio || 1));
    const firstSize = !cssW;
    // keep the scale when the width changes: extend/shrink the visible y-range with the height
    if (cssW && cssH && (nw !== cssW || nh !== cssH)) {
      const cy = (view.ymin + view.ymax) / 2, hy = ((view.ymax - view.ymin) / 2) * (nh / cssH) * (cssW / nw);
      view = { ...view, ymin: cy - hy, ymax: cy + hy };
    }
    cssW = nw; cssH = nh;
    canvas.width = Math.round(nw * dpr);
    canvas.height = Math.round(nh * dpr);
    if (firstSize && items.length) { home = fitView(); view = { ...home }; }
    schedule();
  }
  const ro = typeof win.ResizeObserver === "function" ? new win.ResizeObserver(resize) : null;
  if (ro) ro.observe(wrap); else win.addEventListener("resize", resize);
  resize();
  const mq = win.matchMedia ? win.matchMedia("(prefers-color-scheme: dark)") : null;
  const onScheme = () => { buildLegend(); schedule(); };
  mq?.addEventListener?.("change", onScheme);

  function destroy() {
    destroyed = true;
    if (raf) win.cancelAnimationFrame(raf);
    win.clearTimeout(ariaTimer);
    if (ro) ro.disconnect(); else win.removeEventListener("resize", resize);
    mq?.removeEventListener?.("change", onScheme);
    root.remove();
  }

  return { set, resetView, zoom: (f) => zoom(f), destroy, summary, redraw: () => { buildLegend(); schedule(); }, get view() { return { ...view }; } };
}

function onlyInsideTrig(u, v) {
  const TRIG = new Set(["sin", "cos", "tan", "cot", "sec", "csc"]);
  const walk = (w, inside) => {
    if (w.k === "sym") return w.name !== v || inside;
    const ins = inside || (w.k === "fn" && TRIG.has(w.name));
    return w.args.every((a) => walk(a, ins));
  };
  return walk(u, false);
}
