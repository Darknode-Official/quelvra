// Quelvra function analysis: sign charts of f' and f'', critical points, one-sided boundary values,
// images of domain components (range), extrema, monotonicity and concavity.
//
// Mathematical basis. f is elementary (no floor/sign/...) so it is continuous on its domain; the
// domain splits into components (intervals). On a component, f' (and f'') can change sign only at
// its zeros and at points where it is undefined, so ONE exact test point per piece between such
// cut points decides the sign on the whole piece. The image of a component is the interval between
// the smallest and largest of: f at critical points, f at closed ends, one-sided limits at open
// ends; an end of the image is attained exactly when some attained candidate equals it.
// Periodic f (only through sin/cos/tan... of a*x + b) is analysed on a window of whole periods.

import { diff } from "../calc/diff.js";
import { limit } from "../calc/limit.js";
import { denominators } from "../solve/util.js";
import { X, Q, toText, C, safe, fail, dv, zerosOf, familyMembers, sortUniq, testPoint, signAt, valueAt, fAt, hp, cmpPt, periodOf, assertElementary, ptText, tidy } from "./util.js";
import { domainSet, components } from "./domainset.js";

const NEG_OO = X.mul(X.NEG_ONE, X.OO);

// points where g may change sign without a zero: denominators, fractional-power radicands, abs arguments
function breakExprs(g, x) {
  const out = [];
  const add = (u) => { if (!X.freeOf(u, x) && !out.includes(u)) out.push(u); };
  for (const d of denominators(g)) add(d);
  const walk = (w) => {
    if (w.k === "pow" && X.isNum(w.args[1]) && w.args[1].v.d !== 1n) add(w.args[0]);
    if (w.k === "fn" && w.name === "abs") add(w.args[0]);
    for (const a of w.args || []) walk(a);
  };
  walk(g);
  return out;
}

function pointsIn(z, win, x) {
  const pts = [...z.points];
  if (z.families.length) {
    if (!win) throw fail("infinitely many critical points; give an interval, for example extrema(f, x, a, b)");
    pts.push(...familyMembers(z.families, win.a, win.b));
  }
  return pts;
}

// Sign chart of g over the components. Returns per component { comp, cuts: [point], signs: [s] }
// where signs[i] is the sign of g on the open piece between cuts[i-1] and cuts[i] (component ends
// included as the outermost cuts).
export function chart(g, x, comps, env, win, extraPts = []) {
  const cand = [];
  const z = zerosOf(g, x, env);
  if (z.all) return { constantZero: true, charts: comps.map((comp) => ({ comp, inner: [], signs: [0] })) };
  cand.push(...pointsIn(z, win, x).map((p) => ({ ...p, why: "zero" })));
  for (const b of breakExprs(g, x)) {
    const zb = zerosOf(b, x, env);
    cand.push(...pointsIn(zb, win, x).map((p) => ({ ...p, why: "undefined" })));
  }
  cand.push(...extraPts);
  // a "zero" at which g itself is undefined (0/0 such as x/|x| at 0) is a break, not a stationary point
  for (const p of cand) if (p.why === "zero" && !p.approx && valueAt(g, x, p.tree) === null) p.why = "undefined";
  const all = sortUniq(cand);
  for (const p of all) if (p.why === "zero" && cand.some((q) => q.why === "undefined" && Math.abs(q.v - p.v) <= 1e-12 * Math.max(1, Math.abs(p.v)))) p.why = "undefined";
  const charts = [];
  for (const comp of comps) {
    const inner = all.filter((p) => p.v > comp.lo.v + 1e-12 * Math.max(1, Math.abs(p.v)) && p.v < comp.hi.v - 1e-12 * Math.max(1, Math.abs(p.v)));
    const cuts = [comp.lo.v, ...inner.map((p) => p.v), comp.hi.v];
    const signs = [];
    for (let i = 0; i + 1 < cuts.length; i++) {
      const t = testPoint(cuts[i], cuts[i + 1]);
      let s = signAt(g, x, t);
      if (s === null || s === undefined) {
        const v = fAt(g, x, dv(t));
        if (Number.isFinite(v) && Math.abs(v) > 1e-9) s = v > 0 ? 1 : -1;
        else throw fail(`could not decide the sign of ${toText(g)} at ${x} = ${toText(t)}`);
      }
      signs.push(s);
    }
    charts.push({ comp, inner, signs });
  }
  return { charts, zeros: z };
}

export function analyze(f0, x, env, opts = {}) {
  assertElementary(f0, x);
  const f = C(f0);
  if (f === X.UNDEF) throw fail("the function is undefined everywhere");
  const d = domainSet(f0, x, env);
  let win = opts.window || null, period = null;
  if (!win) {
    period = periodOf(f, x);
    if (period) win = { lo: C(X.neg(period)), hi: C(X.mul(X.TWO, period)), loOpen: false, hiOpen: false, periodic: true };
  }
  if (!win && d.families.length) throw fail("the domain has infinitely many gaps but the function is not periodic in a supported way");
  const w = win ? { a: win.lo === null ? -Infinity : dv(win.lo), b: win.hi === null ? Infinity : dv(win.hi) } : null;
  const wFinite = w && Number.isFinite(w.a) && Number.isFinite(w.b) ? w : null;
  const comps = components(d, win);
  const df = C(diff(f, x));
  if (df.k === "deriv" || X.contains(df, X.UNDEF)) throw fail("could not differentiate f");
  const c1 = chart(df, x, comps, env, wFinite);
  const res = { f0, f, x, d, win, period, comps, df, c1, env };
  // critical points: interior cut points of the f' chart at which f is defined
  const crit = [];
  for (const ch of c1.charts) {
    ch.inner.forEach((p, i) => {
      const value = p.approx ? null : valueAt(f0, x, p.tree);
      if (!p.approx && value === null) return; // not in the domain (should not happen inside a component)
      const sL = ch.signs[i], sR = ch.signs[i + 1];
      const type = sL > 0 && sR < 0 ? "max" : sL < 0 && sR > 0 ? "min" : "none";
      const stationary = p.why === "zero";
      crit.push({ ...p, value, valueV: value ? dv(value) : fAt(f0, x, p.v), type, stationary, comp: ch.comp, sL, sR });
    });
  }
  res.crit = crit;
  return res;
}

// Value of f at a component end: attained value or one-sided limit (with its kind).
export function endValue(res, comp, side) {
  const e = side === "lo" ? comp.lo : comp.hi;
  const { f0, f, x } = res;
  if (!e.open && e.tree) {
    const v = valueAt(f0, x, e.tree);
    if (v === null) throw fail(`f is undefined at the closed end ${toText(e.tree)}`);
    return { tree: v, v: dv(v), attained: true, at: e.tree };
  }
  const to = e.tree === null ? (side === "lo" ? NEG_OO : X.OO) : e.tree;
  const dir = e.tree === null ? "" : side === "lo" ? "+" : "-";
  const r = limit(f, X.sym(x), to, dir, { timeLimit: 2500 });
  if (r.status !== "exact") throw fail(`the limit of f as ${x} -> ${toText(to)}${dir} ${r.status === "dne" ? "does not exist" : "could not be determined"}`);
  const t = r.value;
  const inf = t === X.OO ? 1 : isNegInf(t) ? -1 : 0;
  return { tree: t, v: inf ? inf * Infinity : dv(t), inf, attained: false, limitAt: to, dir };
}
export const isNegInf = (t) => t && t.k === "mul" && t.args.length === 2 && X.isNum(t.args[0]) && t.args[0].v.n < 0n && t.args[1] === X.OO;

function cmpVal(a, b) {
  if (a.inf || b.inf) return (a.inf || 0) === (b.inf || 0) ? 0 : (a.inf || 0) < (b.inf || 0) ? -1 : 1;
  const c = cmpPt({ tree: a.tree, v: a.v, approx: a.approx }, { tree: b.tree, v: b.v, approx: b.approx });
  if (c === null) throw fail(`could not compare ${toText(a.tree)} and ${toText(b.tree)}`);
  return c;
}

// Image of each component and of the whole window. Returns { parts: [{comp, lo, hi}], union: [iv] }
// where lo/hi are value records { tree, v, inf, attained } and iv are interval-set entries.
export function images(res) {
  const parts = [];
  for (const ch of res.c1.charts) {
    const comp = ch.comp;
    const cands = [];
    if (comp.lo.v === comp.hi.v) {
      const v = valueAt(res.f0, res.x, comp.lo.tree);
      if (v === null) continue;
      cands.push({ tree: v, v: dv(v), attained: true, at: comp.lo.tree });
    } else {
      cands.push(endValue(res, comp, "lo"), endValue(res, comp, "hi"));
      for (const c of res.crit.filter((c) => c.comp === comp)) {
        if (c.approx) {
          const h = safe(() => hp(X.subs(res.f, { [res.x]: c.tree }), 30));
          const vv = h && h.ok ? h.re : fAt(res.f0, res.x, c.v);
          cands.push({ tree: X.num(Q.fromDecimal(String(+vv.toPrecision(15)))), v: vv, attained: true, approx: true, at: c.tree });
        } else cands.push({ tree: c.value, v: dv(c.value), attained: true, at: c.tree });
      }
    }
    let lo = cands[0], hi = cands[0];
    for (const c of cands.slice(1)) { if (cmpVal(c, lo) < 0) lo = c; if (cmpVal(c, hi) > 0) hi = c; }
    const loAtt = cands.find((c) => c.attained && cmpVal(c, lo) === 0) || null;
    const hiAtt = cands.find((c) => c.attained && cmpVal(c, hi) === 0) || null;
    parts.push({ comp, lo: loAtt || lo, hi: hiAtt || hi, loAttained: !!loAtt, hiAttained: !!hiAtt, cands });
  }
  // union of the images
  const ivs = parts.map((p) => ({ lo: p.lo.inf === -1 ? null : p.lo, hi: p.hi.inf === 1 ? null : p.hi, loOpen: !p.loAttained, hiOpen: !p.hiAttained }))
    .filter((iv) => !(iv.lo && iv.lo.inf === 1) && !(iv.hi && iv.hi.inf === -1));
  ivs.sort((a, b) => (a.lo === null ? -1 : b.lo === null ? 1 : cmpVal(a.lo, b.lo)));
  const merged = [];
  for (const iv of ivs) {
    const m = merged[merged.length - 1];
    if (m) {
      const touch = m.hi === null ? 1 : iv.lo === null ? 1 : cmpVal(iv.lo, m.hi) < 0 ? 1 : cmpVal(iv.lo, m.hi) === 0 ? (m.hiOpen && iv.loOpen ? 0 : 1) : -1;
      if (touch === 1) {
        if (m.hi !== null && (iv.hi === null || cmpVal(iv.hi, m.hi) > 0)) { m.hi = iv.hi; m.hiOpen = iv.hiOpen; }
        else if (m.hi !== null && iv.hi !== null && cmpVal(iv.hi, m.hi) === 0) m.hiOpen = m.hiOpen && iv.hiOpen;
        continue;
      }
    }
    merged.push({ ...iv });
  }
  const union = merged.map((iv) => ({ lo: iv.lo ? iv.lo.tree : null, hi: iv.hi ? iv.hi.tree : null, loOpen: iv.lo === null ? true : iv.loOpen, hiOpen: iv.hi === null ? true : iv.hiOpen, loRec: iv.lo, hiRec: iv.hi }));
  return { parts, union };
}

// Monotone pieces: maximal open intervals of constant f' sign (merged across critical points
// where the sign does not change, since f is continuous there).
export function monotonePieces(res, which = res.c1) {
  const out = [];
  for (const ch of which.charts) {
    let start = ch.comp.lo, s = ch.signs[0];
    for (let i = 0; i < ch.inner.length; i++) {
      const p = ch.inner[i];
      const inDomain = p.approx ? true : valueAt(res.f0, res.x, p.tree) !== null;
      if (ch.signs[i + 1] === s && inDomain) continue;
      out.push({ lo: start, hi: { tree: p.tree, v: p.v, approx: p.approx }, sign: s, comp: ch.comp });
      start = { tree: p.tree, v: p.v, approx: p.approx };
      s = ch.signs[i + 1];
    }
    out.push({ lo: start, hi: ch.comp.hi, sign: s, comp: ch.comp });
  }
  return out;
}

export function secondChart(res) {
  if (res.c2) return res.c2;
  const d2 = C(diff(res.df, res.x));
  if (d2.k === "deriv" || X.contains(d2, X.UNDEF)) throw fail("could not compute f''");
  const w = res.win ? { a: res.win.lo === null ? -Infinity : dv(res.win.lo), b: res.win.hi === null ? Infinity : dv(res.win.hi) } : null;
  const extra = res.crit.filter((c) => !c.stationary).map((c) => ({ tree: c.tree, v: c.v, approx: c.approx, why: "undefined" }));
  res.d2 = d2;
  res.c2 = chart(d2, res.x, res.comps, res.env, w && Number.isFinite(w.a) && Number.isFinite(w.b) ? w : null, extra);
  return res.c2;
}

// Inflection points: interior cut points of the f'' chart where f is defined and f'' changes sign.
export function inflections(res) {
  const c2 = secondChart(res);
  const out = [];
  if (c2.constantZero) return out;
  for (const ch of c2.charts) ch.inner.forEach((p, i) => {
    const sL = ch.signs[i], sR = ch.signs[i + 1];
    if (!(sL * sR < 0)) return;
    const value = p.approx ? null : valueAt(res.f0, res.x, p.tree);
    if (!p.approx && value === null) return;
    out.push({ ...p, value, sL, sR, comp: ch.comp });
  });
  return out;
}

export { ptText, tidy, NEG_OO };
