// Finite sets, counting by inclusion-exclusion, relations and functions.
//
//   setcalc(expr)          expr over lists (sets) and tuples with SUNION SINTER SMINUS SSYMDIFF SCOMPL(A, U) SCART SPOWER
//   divcount(lo, hi, [d1, ..., dk], mode)   integers in [lo, hi] divisible by at least one d (mode 1) / by none (mode 0) / by all (mode 2)
//   unionsize(k, [mask, size], ...)         |A1 ∪ ... ∪ Ak| from the sizes of all intersections (mask = subset of sets)
//   relprops(pairs | reldivides(1) | relcongmod(m) | relleq(1) | rellt(1), domain)
//   funcprops(pairs | fromformula(expr[, x]), domain[, codomain])
//   fcompose(f, g)         f ∘ g, that is x -> f(g(x))
//
// Verification: set results are re-derived element by element from a membership predicate and
// checked against counting identities; inclusion-exclusion counts are checked by brute force or by
// the Venn-region decomposition; relation properties by boolean matrix algebra (R^T, R∘R); function
// properties by image counting.

import { refuse, ansNum, ansText, ansYes, check, step, fmtVal, cmpVal, keyOf, N, gcd, lcm } from "./util.js";
import { valueOf, intOf, listOf, labelOf, ratOf } from "./decode.js";

const uniq = (xs) => { const m = new Map(); for (const x of xs) m.set(keyOf(x), x); return [...m.values()].sort(cmpVal); };
const S = (xs) => ({ set: uniq(xs) });
const fmt = (xs) => fmtVal({ set: uniq(xs) });

// ---------------------------------------------------------------- set expressions
const SETOPS = new Set(["SUNION", "SINTER", "SMINUS", "SSYMDIFF", "SCOMPL", "SCART", "SPOWER"]);
function setOf(u) { const v = valueOf(u); if (!v || !v.set) throw refuse("expected a set"); return v.set; }
function evalSet(u) {
  if (u.k === "fn" && SETOPS.has(u.name)) {
    const a = u.args.map(evalSet);
    const has = (xs, x) => xs.some((y) => keyOf(y) === keyOf(x));
    switch (u.name) {
      case "SUNION": return uniq(a.flat());
      case "SINTER": return uniq(a[0].filter((x) => a.slice(1).every((b) => has(b, x))));
      case "SMINUS": if (a.length !== 2) throw refuse("difference takes two sets"); return uniq(a[0].filter((x) => !has(a[1], x)));
      case "SSYMDIFF": if (a.length !== 2) throw refuse("symmetric difference takes two sets"); return uniq([...a[0].filter((x) => !has(a[1], x)), ...a[1].filter((x) => !has(a[0], x))]);
      case "SCOMPL": if (a.length !== 2) throw refuse("complement needs a set and a universe"); if (!a[0].every((x) => has(a[1], x))) throw refuse("the set is not contained in the universe"); return uniq(a[1].filter((x) => !has(a[0], x)));
      case "SCART": { if (a.length !== 2) throw refuse("cartesian product takes two sets"); if (a[0].length * a[1].length > 4096) throw refuse("the product is too large to list"); const out = []; for (const x of a[0]) for (const y of a[1]) out.push([x, y]); return uniq(out); }
      case "SPOWER": { if (a.length !== 1) throw refuse("power set takes one set"); const b = uniq(a[0]); if (b.length > 10) throw refuse("the power set is listed for sets of at most 10 elements"); const out = []; for (let m = 0; m < 1 << b.length; m++) out.push({ set: b.filter((_, i) => m & (1 << i)) }); return out.sort(cmpVal); }
    }
  }
  return uniq(setOf(u));
}
// membership predicate: an independent recursive definition
function member(x, u) {
  if (u.k === "fn" && SETOPS.has(u.name)) {
    const [A, B] = u.args;
    switch (u.name) {
      case "SUNION": return u.args.some((a) => member(x, a));
      case "SINTER": return u.args.every((a) => member(x, a));
      case "SMINUS": return member(x, A) && !member(x, B);
      case "SSYMDIFF": return member(x, A) !== member(x, B);
      case "SCOMPL": return member(x, B) && !member(x, A);
      case "SCART": return Array.isArray(x) && x.length === 2 && member(x[0], A) && member(x[1], B);
      case "SPOWER": return !!(x && x.set) && x.set.every((y) => member(y, A));
    }
  }
  const k = keyOf(x);
  return setOf(u).some((y) => keyOf(y) === k);
}
const leafElems = (u) => (u.k === "fn" && SETOPS.has(u.name) ? u.args.flatMap(leafElems) : setOf(u));
// expected cardinality from counting formulas (independent of the listing)
function cardFormula(u) {
  if (!(u.k === "fn" && SETOPS.has(u.name))) return uniq(setOf(u)).length;
  if (u.name === "SCART") return cardFormula(u.args[0]) * cardFormula(u.args[1]);
  if (u.name === "SPOWER") return 2 ** cardFormula(u.args[0]);
  return null;
}
function cmdSetCalc(args) {
  if (args.length !== 1) throw refuse("setcalc takes one set expression");
  const u = args[0];
  const res = evalSet(u);
  const top = u.k === "fn" ? u.name : "";
  const label = top === "SPOWER" ? "power set" : "result";
  return {
    answers: [ansText(label, fmtVal({ set: res })), ansNum("cardinality", res.length)],
    steps: [step("sets.calc", { SUNION: "Union: everything in either set", SINTER: "Intersection: what the sets share", SMINUS: "Difference: in the first set but not the second", SSYMDIFF: "Symmetric difference: in exactly one of the sets", SCOMPL: "Complement: everything in the universe outside the set", SCART: "Cartesian product: all ordered pairs", SPOWER: "Power set: all subsets" }[top] || "List the distinct elements", `The result has ${res.length} element(s).`)],
    checks: () => {
      const cs = [check("membership", res.every((x) => member(x, u)), "every listed element satisfies the membership condition")];
      const f = cardFormula(u);
      if (f !== null) cs.push(check("counting", f === res.length, top === "SPOWER" ? `|P(A)| = 2^|A| = ${f}` : top === "SCART" ? `|A × B| = |A| |B| = ${f}` : `${f} distinct elements`));
      else {
        const missing = uniq(leafElems(u)).filter((x) => member(x, u) && !res.some((y) => keyOf(y) === keyOf(x)));
        cs.push(check("completeness", missing.length === 0, "no element of the given sets that belongs to the result is missing"));
      }
      if (top === "SUNION" && u.args.length === 2) {
        const [a, b] = u.args.map(evalSet); const i = evalSet({ k: "fn", name: "SINTER", args: u.args });
        cs.push(check("inclusion-exclusion", res.length === a.length + b.length - i.length, `|A ∪ B| = |A| + |B| - |A ∩ B| = ${a.length} + ${b.length} - ${i.length}`));
      }
      return cs;
    },
  };
}

// ---------------------------------------------------------------- counting
function cmdDivCount(args) {
  const [lo, hi] = [intOf(args[0]), intOf(args[1])];
  const ds = listOf(args[2], "a list of divisors").map((d) => intOf(d));
  const mode = Number(intOf(args[3] || { k: "num", v: N.Q(1n) }));
  if (ds.some((d) => d <= 0n)) throw refuse("divisors must be positive");
  if (ds.length > 12) throw refuse("at most 12 divisors");
  if (hi < lo) throw refuse("empty range");
  const cntDiv = (m) => { const f = (x) => (x >= 0n ? x / m : -((-x + m - 1n) / m)); return f(hi) - f(lo - 1n); };
  // inclusion-exclusion over non-empty subsets
  let atLeast = 0n;
  const terms = [];
  for (let s = 1; s < 1 << ds.length; s++) {
    const sub = ds.filter((_, i) => s & (1 << i));
    const L = sub.reduce((a, b) => lcm(a, b), 1n);
    const c = cntDiv(L);
    const sign = sub.length % 2 ? 1n : -1n;
    atLeast += sign * c;
    if (ds.length <= 4) terms.push(`${sign > 0n ? "+" : "-"} ⌊${hi}/${L}⌋`);
  }
  const total = hi - lo + 1n;
  const all = cntDiv(ds.reduce((a, b) => lcm(a, b), 1n));
  const value = mode === 1 ? atLeast : mode === 0 ? total - atLeast : all;
  return {
    answers: [ansNum("count", value)],
    steps: [step("sets.ie", mode === 2 ? "Divisible by all of them means divisible by their lcm" : "Inclusion-exclusion over the divisibility conditions", mode === 2 ? `lcm = ${ds.reduce((a, b) => lcm(a, b), 1n)}` : `Numbers divisible by at least one: ${atLeast}${terms.length && lo === 1n ? ` (${terms.join(" ").replace(/^\+ /, "")})` : ""}.`),
      ...(mode === 0 ? [step("sets.complement", "Subtract from the total", `${total} - ${atLeast} = ${value}.`)] : [])],
    checks: () => {
      if (total <= 2000000n) {
        let c = 0n;
        for (let x = lo; x <= hi; x++) { const hits = ds.filter((d) => x % d === 0n).length; if (mode === 1 ? hits > 0 : mode === 0 ? hits === 0 : hits === ds.length) c++; }
        return [check("brute force", c === value, `checking each of the ${total} integers gives ${c}`)];
      }
      // periodicity: the pattern repeats with period L = lcm; count one period by brute force
      const L = ds.reduce((a, b) => lcm(a, b), 1n);
      if (L > 2000000n) return [check("brute force", false, "range and period too large for a direct count")];
      const inPeriod = (x) => { const hits = ds.filter((d) => x % d === 0n).length; return mode === 1 ? hits > 0 : mode === 0 ? hits === 0 : hits === ds.length; };
      let c = 0n; const full = total / L; let per = 0n;
      for (let x = 0n; x < L; x++) if (inPeriod(lo + x)) per++;
      c = per * full;
      for (let x = lo + full * L; x <= hi; x++) if (inPeriod(x)) c++;
      return [check("periodic count", c === value, `counting one period of length ${L} and the remainder gives ${c}`)];
    },
  };
}
function cmdUnionSize(args) {
  const k = Number(intOf(args[0]));
  if (k < 2 || k > 5) throw refuse("between 2 and 5 sets");
  const sizes = new Map();
  for (const a of args.slice(1)) { const [m, s] = listOf(a).map((x) => intOf(x)); sizes.set(Number(m), s); }
  for (let m = 1; m < 1 << k; m++) if (!sizes.has(m)) throw refuse("the size of every intersection is needed for inclusion-exclusion");
  let u = 0n;
  for (const [m, s] of sizes) u += (popc(m) % 2 ? 1n : -1n) * s;
  const names = "ABCDE".slice(0, k).split("");
  return {
    answers: [ansNum("count", u)],
    steps: [step("sets.ie", "Inclusion-exclusion", `|${names.join(" ∪ ")}| = Σ|single sets| - Σ|pairwise intersections| + ... = ${u}.`)],
    checks: () => {
      // Venn regions: region(m) = elements in exactly the sets of m; recover by Mobius inversion from supersets
      const region = new Map();
      for (let m = (1 << k) - 1; m >= 1; m--) { let r = sizes.get(m); for (let t = m + 1; t < 1 << k; t++) if ((t & m) === m) r -= region.get(t); region.set(m, r); }
      const neg = [...region.values()].some((r) => r < 0n);
      const sum = [...region.values()].reduce((a, b) => a + b, 0n);
      return [check("Venn regions", !neg && sum === u, neg ? "the given sizes are inconsistent: some Venn region would have negative size" : `the ${(1 << k) - 1} Venn regions have non-negative sizes adding up to ${sum}`)];
    },
  };
}
const popc = (m) => { let c = 0; while (m) { c += m & 1; m >>= 1; } return c; };

// ---------------------------------------------------------------- relations
function pairsOf(u, dom) {
  if (u.k === "fn") {
    const test = { reldivides: (a, b) => (a === 0n ? b === 0n : b % a === 0n), relleq: (a, b) => a <= b, rellt: (a, b) => a < b, relcongmod: null }[u.name];
    let f = test;
    if (u.name === "relcongmod") { const m = intOf(u.args[0], "a modulus"); if (m <= 0n) throw refuse("the modulus must be positive"); f = (a, b) => ((a - b) % m) === 0n; }
    if (!f) throw refuse(`unknown relation ${u.name}`);
    if (dom.some((x) => typeof x !== "bigint")) throw refuse("this relation needs an integer domain");
    const out = []; for (const a of dom) for (const b of dom) if (f(a, b)) out.push([a, b]);
    return out;
  }
  const ps = listOf(u, "a set of ordered pairs").map(valueOf);
  if (ps.some((p) => !Array.isArray(p) || p.length !== 2)) throw refuse("a relation is a set of ordered pairs (a, b)");
  return uniq(ps);
}
function cmdRelProps(args) {
  if (args.length < 1 || args.length > 2) throw refuse("relprops(relation, domain)");
  let dom = args[1] ? uniq(setOf(args[1])) : null;
  if (!dom && args[0].k === "fn") throw refuse("give the set the relation is on");
  const R = pairsOf(args[0], dom || []);
  if (!dom) dom = uniq(R.flat());
  if (dom.length > 200) throw refuse("the domain is too large");
  const K = (x) => keyOf(x);
  const inDom = new Set(dom.map(K));
  if (R.some(([a, b]) => !inDom.has(K(a)) || !inDom.has(K(b)))) throw refuse("the relation uses elements outside the given set");
  const has = new Set(R.map(([a, b]) => `${K(a)}|${K(b)}`));
  const rel = (a, b) => has.has(`${K(a)}|${K(b)}`);
  const refl = dom.every((a) => rel(a, a));
  const sym = R.every(([a, b]) => rel(b, a));
  const anti = R.every(([a, b]) => K(a) === K(b) || !rel(b, a));
  const trans = R.every(([a, b]) => R.every(([c, d]) => K(b) !== K(c) || rel(a, d)));
  const equiv = refl && sym && trans, po = refl && anti && trans;
  const answers = [ansYes("reflexive", refl), ansYes("symmetric", sym), ansYes("antisymmetric", anti), ansYes("transitive", trans), ansYes("equivalence relation", equiv), ansYes("partial order", po)];
  let classes = null, hasse = null;
  if (equiv) {
    classes = []; const seen = new Set();
    for (const a of dom) { if (seen.has(K(a))) continue; const c = dom.filter((b) => rel(a, b)); c.forEach((b) => seen.add(K(b))); classes.push(c); }
    answers.push(ansText("equivalence classes", fmtVal({ set: classes.map((c) => ({ set: c })).sort(cmpVal) })), ansNum("number of classes", classes.length));
  }
  if (po) {
    hasse = R.filter(([a, b]) => K(a) !== K(b) && !dom.some((c) => K(c) !== K(a) && K(c) !== K(b) && rel(a, c) && rel(c, b)));
    answers.push(ansText("hasse edges", fmt(hasse)));
    const minimal = dom.filter((b) => !dom.some((a) => K(a) !== K(b) && rel(a, b)));
    const maximal = dom.filter((a) => !dom.some((b) => K(a) !== K(b) && rel(a, b)));
    answers.push(ansText("minimal elements", fmt(minimal)), ansText("maximal elements", fmt(maximal)));
  }
  const reasons = [];
  if (!refl) { const a = dom.find((x) => !rel(x, x)); reasons.push(`not reflexive: (${fmtVal(a)}, ${fmtVal(a)}) is missing`); }
  if (!sym) { const p = R.find(([a, b]) => !rel(b, a)); reasons.push(`not symmetric: (${fmtVal(p[0])}, ${fmtVal(p[1])}) is in R but (${fmtVal(p[1])}, ${fmtVal(p[0])}) is not`); }
  if (!trans) { for (const [a, b] of R) { const q = R.find(([c, d]) => K(b) === K(c) && !rel(a, d)); if (q) { reasons.push(`not transitive: (${fmtVal(a)}, ${fmtVal(b)}) and (${fmtVal(q[0])}, ${fmtVal(q[1])}) are in R but (${fmtVal(a)}, ${fmtVal(q[1])}) is not`); break; } } }
  return {
    answers,
    steps: [step("sets.relation", `Test the relation (${R.length} pairs) on a set of ${dom.length} elements`, reasons.join("; ") || "All the defining conditions were checked pair by pair.")],
    checks: () => {
      // boolean matrix route
      const n = dom.length, idx = new Map(dom.map((x, i) => [K(x), i]));
      const M = Array.from({ length: n }, () => Array(n).fill(false));
      for (const [a, b] of R) M[idx.get(K(a))][idx.get(K(b))] = true;
      const refl2 = M.every((r, i) => r[i]);
      const sym2 = M.every((r, i) => r.every((v, j) => v === M[j][i]));
      const anti2 = M.every((r, i) => r.every((v, j) => i === j || !(v && M[j][i])));
      let trans2 = true;
      for (let i = 0; i < n && trans2; i++) for (let j = 0; j < n && trans2; j++) { let sq = false; for (let k = 0; k < n; k++) if (M[i][k] && M[k][j]) { sq = true; break; } if (sq && !M[i][j]) trans2 = false; }
      const cs = [check("relation matrix", refl2 === refl && sym2 === sym && anti2 === anti && trans2 === trans, "the diagonal, M = Mᵀ, M ∧ Mᵀ ⊆ I and M∘M ⊆ M tests on the relation matrix agree")];
      if (classes) {
        const cover = classes.flat().length === n && new Set(classes.flat().map(K)).size === n;
        const exact = dom.every((a) => dom.every((b) => M[idx.get(K(a))][idx.get(K(b))] === classes.some((c) => c.some((x) => K(x) === K(a)) && c.some((x) => K(x) === K(b)))));
        cs.push(check("partition", cover && exact, "the classes partition the set, and two elements are related exactly when they share a class"));
      }
      if (hasse) {
        // strict part S = M minus identity; covering relation = S minus S∘S
        const Sx = M.map((r, i) => r.map((v, j) => v && i !== j));
        const cov = [];
        for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) { if (!Sx[i][j]) continue; let two = false; for (let k = 0; k < n; k++) if (Sx[i][k] && Sx[k][j]) { two = true; break; } if (!two) cov.push(`${i},${j}`); }
        const mine = new Set(hasse.map(([a, b]) => `${idx.get(K(a))},${idx.get(K(b))}`));
        cs.push(check("covering relation", cov.length === mine.size && cov.every((c) => mine.has(c)), "S \\ (S∘S) for the strict order S gives the same Hasse edges"));
      }
      return cs;
    },
  };
}

// ---------------------------------------------------------------- functions
function evalInt(u, env) {
  switch (u.k) {
    case "num": return u.v;
    case "sym": { const v = env[u.name]; if (v === undefined) throw refuse(`unknown variable ${u.name}`); return N.Q(v); }
    case "add": return u.args.map((a) => evalInt(a, env)).reduce(N.add);
    case "mul": return u.args.map((a) => evalInt(a, env)).reduce(N.mul);
    case "pow": { const b = evalInt(u.args[0], env), e = evalInt(u.args[1], env); if (e.d !== 1n || e.n < 0n || e.n > 256n) throw refuse("powers must be small non-negative integers"); return N.pow(b, e.n); }
    case "fn": {
      const a = u.args.map((x) => evalInt(x, env));
      if (u.name === "mod" && a.length === 2) { if (a[0].d !== 1n || a[1].d !== 1n || a[1].n === 0n) throw refuse("mod needs integers"); const m = a[1].n < 0n ? -a[1].n : a[1].n; return N.Q(((a[0].n % m) + m) % m); }
      if (u.name === "abs") return N.abs(a[0]);
      if (u.name === "floor") return N.Q(N.floor(a[0]));
      throw refuse(`cannot evaluate ${u.name}`);
    }
  }
  const r = ratOf(u); if (r) return r;
  throw refuse("cannot evaluate the formula");
}
function funcPairs(u, dom) {
  if (u.k === "fn" && u.name === "fromformula") {
    const x = u.args[1] ? labelOf(u.args[1]) : "x";
    return dom.map((a) => { if (typeof a !== "bigint") throw refuse("a formula needs an integer domain"); const v = evalInt(u.args[0], { [x]: a }); if (v.d !== 1n) throw refuse("the formula gives a non-integer value"); return [a, v.n]; });
  }
  return pairsOf(u, dom);
}
function cmdFuncProps(args) {
  if (args.length < 1 || args.length > 3) throw refuse("funcprops(f, domain, codomain)");
  let dom = args[1] ? uniq(setOf(args[1])) : null;
  if (!dom && args[0].k === "fn") throw refuse("give the domain of the function");
  const F = funcPairs(args[0], dom || []);
  if (!dom) dom = uniq(F.map((p) => p[0]));
  const cod = args[2] ? uniq(setOf(args[2])) : dom;
  const K = keyOf;
  // is it a function from dom to cod?
  const outs = new Map();
  for (const [a, b] of F) { if (!outs.has(K(a))) outs.set(K(a), []); outs.get(K(a)).push(b); }
  const problems = [];
  for (const a of dom) { const o = outs.get(K(a)) || []; if (uniq(o).length !== 1) problems.push(`${fmtVal(a)} has ${o.length ? "several images" : "no image"}`); }
  for (const [a, b] of F) { if (!dom.some((x) => K(x) === K(a))) problems.push(`${fmtVal(a)} is not in the domain`); if (!cod.some((y) => K(y) === K(b))) problems.push(`${fmtVal(b)} is not in the codomain`); }
  if (problems.length) {
    return { answers: [ansYes("function", false), ansText("reason", problems.slice(0, 3).join("; "))], steps: [step("sets.function", "Check that each domain element has exactly one image in the codomain", problems[0])],
      checks: () => [check("definition", dom.some((a) => (outs.get(K(a)) || []).length !== 1 || uniq(outs.get(K(a))).length !== 1) || F.some(([a, b]) => !dom.some((x) => K(x) === K(a)) || !cod.some((y) => K(y) === K(b))), problems[0])] };
  }
  const img = (a) => outs.get(K(a))[0];
  let inj = true, witness = null;
  for (let i = 0; i < dom.length && inj; i++) for (let j = i + 1; j < dom.length; j++) if (K(img(dom[i])) === K(img(dom[j]))) { inj = false; witness = [dom[i], dom[j]]; break; }
  const missing = cod.filter((y) => !dom.some((a) => K(img(a)) === K(y)));
  const surj = missing.length === 0;
  const answers = [ansYes("injective", inj), ansYes("surjective", surj), ansYes("bijective", inj && surj), ansText("image", fmt(dom.map(img)))];
  return {
    answers,
    steps: [step("sets.function", "Injective: no two inputs share an output; surjective: every codomain element is hit", [inj ? "no repeated output" : `f(${fmtVal(witness[0])}) = f(${fmtVal(witness[1])}) = ${fmtVal(img(witness[0]))}`, surj ? "every element of the codomain is an output" : `${fmt(missing)} ${missing.length === 1 ? "is" : "are"} never an output`].join("; ") + ".")],
    checks: () => {
      const imageSize = new Set(dom.map((a) => K(img(a)))).size;
      return [check("image count", (imageSize === dom.length) === inj && (imageSize === cod.length && dom.every((a) => cod.some((y) => K(y) === K(img(a))))) === surj, `|image| = ${imageSize}, |domain| = ${dom.length}, |codomain| = ${cod.length}`)];
    },
  };
}
function cmdCompose(args) {
  if (args.length !== 2) throw refuse("fcompose(f, g) takes two functions");
  const f = pairsOf(args[0], []), g = pairsOf(args[1], []);
  const K = keyOf;
  const fmap = new Map();
  for (const [a, b] of f) { if (fmap.has(K(a)) && K(fmap.get(K(a))) !== K(b)) throw refuse("f is not a function (an input has two images)"); fmap.set(K(a), b); }
  const gdom = new Set();
  for (const [a] of g) { if (gdom.has(K(a))) throw refuse("g is not a function (an input has two images)"); gdom.add(K(a)); }
  const out = [];
  for (const [a, b] of g) { if (!fmap.has(K(b))) throw refuse(`f(g(${fmtVal(a)})) = f(${fmtVal(b)}) is not defined`); out.push([a, fmap.get(K(b))]); }
  const res = uniq(out);
  return {
    answers: [ansText("composition", fmt(res))],
    steps: [step("sets.compose", "(f ∘ g)(x) = f(g(x)): apply g first, then f", res.map(([a, c]) => `f(g(${fmtVal(a)})) = ${fmtVal(c)}`).join(", "))],
    checks: () => {
      // relation composition g ; f computed from the pair lists by a join
      const joined = uniq(g.flatMap(([a, b]) => f.filter(([c]) => K(c) === K(b)).map(([, d]) => [a, d])));
      return [check("relational join", joined.length === res.length && joined.every((p, i) => K(p) === K(res[i])), "joining the pairs of g with the pairs of f gives the same set")];
    },
  };
}
void gcd;

export const SET_HANDLERS = { setcalc: cmdSetCalc, divcount: cmdDivCount, unionsize: cmdUnionSize, relprops: cmdRelProps, funcprops: cmdFuncProps, fcompose: cmdCompose };
