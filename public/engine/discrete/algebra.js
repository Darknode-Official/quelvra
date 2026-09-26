// Abstract algebra: permutations, Z_n and U(n), finite abelian groups, GF(p) and GF(p^k)
// arithmetic, factoring and irreducibility over GF(p) and Q, Gaussian integers, quotient rings.
//
//   perminfo(c1, c2, ...)          product of cycles pcycle(...) / one-line vectors / nested cycle lists
//   permcompose(a, b, ...)         product a b ... (rightmost applied first)
//   elementorder(a, n, kind)       kind 0: additive order in Z_n, 1: multiplicative order mod n
//   unitgroup(n)  cyclicgroup(n)  abeliangroups(n)
//   gfcalc(expr, p[, modulus])     arithmetic in GF(p) or GF(p)[x]/(modulus)
//   factormod(f, p)  isirreducible(f, p)   (p = 0 means over Q)
//   gaussgcd(a, b)  gaussfactor(z)  quotientring(f[, p])   (no p: over Z)
//
// Independent checks: brute-force powering for orders, inversion counts for signs, element-order
// distributions for group structures, divisor-chain enumeration for abelian groups, companion
// matrices for field arithmetic, Rabin's test against trial division, exact products for every
// factorisation, and Bezout certificates for Gaussian gcds.

import { refuse, ansNum, ansText, ansYes, ansTree, check, step, N, X, gcd, lcm, mod, modInv, powMod, powModRL, factorSmall, isPrimeSmall, babs } from "./util.js";
import { intOf, listOf, isList, intPolyOf, polyOf, ratOf } from "./decode.js";
import * as P from "./gfpoly.js";
import { factorZ } from "../poly-factor.js";
import { simplify } from "../simplify.js";

// ---------------------------------------------------------------- permutations
// a permutation is a Map point -> image over the points 1..n (identity elsewhere)
function cycleFn(pts) { const m = new Map(); pts.forEach((a, i) => m.set(a, pts[(i + 1) % pts.length])); return m; }
function permOf(u) {
  if (u.k === "fn" && u.name === "pcycle") {
    const pts = u.args.map((a) => Number(intOf(a, "a point")));
    if (new Set(pts).size !== pts.length) throw refuse("a cycle cannot repeat a point");
    return cycleFn(pts);
  }
  if (isList(u)) {
    const items = listOf(u);
    if (items.length && items.every(isList)) return compose(items.map((c) => cycleFn(listOf(c).map((a) => Number(intOf(a, "a point")))))); // list of cycles
    const img = items.map((a) => Number(intOf(a, "a point")));
    const n = img.length;
    if ([...img].sort((a, b) => a - b).some((v, i) => v !== i + 1)) throw refuse("one-line notation must list 1..n exactly once");
    return new Map(img.map((v, i) => [i + 1, v]));
  }
  throw refuse("expected a permutation such as (1 2 3)(4 5) or [2, 3, 1]");
}
const ap = (m, x) => (m.has(x) ? m.get(x) : x);
// product a1 a2 ... ak: apply ak first
function compose(ms) {
  const pts = new Set(ms.flatMap((m) => [...m.keys()]));
  const out = new Map();
  for (const x of pts) { let y = x; for (let i = ms.length - 1; i >= 0; i--) y = ap(ms[i], y); out.set(x, y); }
  return out;
}
function support(m) { return [...m.keys()].filter((x) => ap(m, x) !== x).sort((a, b) => a - b); }
function cyclesOf(m) {
  const seen = new Set(), out = [];
  for (const x of [...m.keys()].sort((a, b) => a - b)) {
    if (seen.has(x) || ap(m, x) === x) continue;
    const c = []; let y = x;
    while (!seen.has(y)) { seen.add(y); c.push(y); y = ap(m, y); }
    out.push(c);
  }
  return out;
}
const cycText = (cs) => (cs.length ? cs.map((c) => `(${c.join(" ")})`).join("") : "()");
const isId = (m) => support(m).length === 0;
const inverseOf = (m) => new Map([...m.entries()].map(([a, b]) => [b, a]));
function permFacts(m) {
  const cs = cyclesOf(m);
  const order = cs.reduce((a, c) => a * BigInt(c.length) / gcd(a, BigInt(c.length)), 1n);
  const sign = cs.reduce((s, c) => s * (c.length % 2 ? 1 : -1), 1);
  return { cs, order, sign };
}
function permChecks(m, facts) {
  return () => {
    const cs = [];
    // order by repeated composition
    let k = 1n, q = m;
    while (!isId(q) && k <= 100000n) { q = compose([m, q]); k++; }
    cs.push(check("powers", k === facts.order, `composing the permutation with itself, the identity first appears at power ${k}`));
    // sign by counting inversions of the one-line form on 1..n
    const n = Math.max(0, ...m.keys());
    const line = Array.from({ length: n }, (_, i) => ap(m, i + 1));
    let inv = 0; for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) if (line[i] > line[j]) inv++;
    cs.push(check("inversions", (inv % 2 ? -1 : 1) === facts.sign, `the one-line form [${line.join(", ")}] has ${inv} inversions`));
    // cycles rebuild the permutation
    const rebuilt = compose(facts.cs.map(cycleFn));
    cs.push(check("cycles", [...m.keys()].every((x) => ap(rebuilt, x) === ap(m, x)), "multiplying the disjoint cycles back together gives the same permutation"));
    return cs;
  };
}
function cmdPermInfo(args) {
  if (!args.length) throw refuse("give a permutation");
  const ms = args.map(permOf);
  const m = compose(ms);
  if (Math.max(0, ...m.keys()) > 1000) throw refuse("points must be at most 1000");
  const f = permFacts(m);
  const inv = inverseOf(m);
  const n = Math.max(0, ...m.keys());
  const answers = [ansText("cycles", cycText(f.cs)), ansNum("order", f.order), ansNum("sign", f.sign), ansText("parity", f.sign === 1 ? "even" : "odd"), ansText("inverse", cycText(cyclesOf(inv))), ansText("one-line", `[${Array.from({ length: n }, (_, i) => ap(m, i + 1)).join(", ")}]`)];
  if (ms.length > 1) answers.push(ansText("product", cycText(f.cs)));
  return {
    answers,
    steps: [
      ...(ms.length > 1 ? [step("perm.product", "Multiply right to left", "Follow each point through the rightmost factor first.")] : []),
      step("perm.cycles", "Disjoint cycle decomposition", cycText(f.cs)),
      step("perm.order", "Order = lcm of the cycle lengths", `lcm(${f.cs.map((c) => c.length).join(", ") || 1}) = ${f.order}.`),
      step("perm.sign", "Sign = (-1)^(number of even-length cycles)", `${f.sign === 1 ? "even" : "odd"} permutation.`),
    ],
    checks: () => [...permChecks(m, f)(), check("inverse", isId(compose([m, inv])) && isId(compose([inv, m])), "the permutation times its inverse is the identity")],
  };
}
function cmdPermCompose(args) {
  if (args.length < 2) throw refuse("permcompose needs at least two permutations");
  const ms = args.map(permOf);
  const m = compose(ms);
  const f = permFacts(m);
  return {
    answers: [ansText("product", cycText(f.cs)), ansNum("order", f.order), ansNum("sign", f.sign)],
    steps: [step("perm.product", "Multiply right to left", "Each point goes through the rightmost permutation first, then the next one to the left."), step("perm.cycles", "Write the result in disjoint cycles", cycText(f.cs))],
    checks: () => {
      // pointwise, via one-line arrays on 1..n
      const n = Math.max(0, ...ms.flatMap((q) => [...q.keys()]));
      const lines = ms.map((q) => Array.from({ length: n + 1 }, (_, i) => ap(q, i)));
      let ok = true;
      for (let x = 1; x <= n; x++) { let y = x; for (let i = lines.length - 1; i >= 0; i--) y = lines[i][y]; if (y !== ap(m, x)) ok = false; }
      return [check("pointwise", ok, "tracing every point through the factors (rightmost first) agrees"), ...permChecks(m, f)()];
    },
  };
}

// ---------------------------------------------------------------- Z_n, U(n)
function totient(n) { const f = factorSmall(n); if (!f) throw refuse("n is too large to factor"); return f.reduce((a, [p, e]) => a * (p - 1n) * p ** BigInt(e - 1), 1n); }
function multOrder(a, n) { // via the factorisation of phi(n)
  const ph = totient(n);
  let k = ph;
  for (const [p] of factorSmall(ph)) while (k % p === 0n && powMod(a, k / p, n) === 1n) k /= p;
  return k;
}
function cmdElementOrder(args) {
  const a = intOf(args[0]), n = intOf(args[1]), kind = Number(intOf(args[2] || X.num(1)));
  if (n < 1n) throw refuse("the modulus must be positive");
  if (kind === 0) {
    const k = n / gcd(mod(a, n), n);
    return {
      answers: [ansNum("order", k)],
      steps: [step("group.addorder", `In Z_${n} the order of ${mod(a, n)} is n / gcd(a, n)`, `${n} / gcd(${mod(a, n)}, ${n}) = ${k}.`)],
      checks: () => {
        const cs = [check("multiple", mod(a * k, n) === 0n, `${k} · ${a} ≡ 0 (mod ${n})`)];
        let ok = true; for (const [p] of factorSmall(k)) if (mod(a * (k / p), n) === 0n) ok = false;
        cs.push(check("minimal", ok, "no proper divisor k/p of the order already gives 0"));
        return cs;
      },
    };
  }
  if (gcd(a, n) !== 1n) throw refuse(`${a} is not invertible mod ${n} (gcd ${gcd(a, n)}), so it has no multiplicative order`);
  const k = multOrder(mod(a, n), n);
  return {
    answers: [ansNum("order", k)],
    steps: [step("group.multorder", `The order divides φ(${n}) = ${totient(n)}`, `Remove prime factors while a^(k/p) ≡ 1; the smallest exponent left is ${k}.`)],
    checks: () => {
      const cs = [check("power", powModRL(a, k, n) === 1n, `${a}^${k} ≡ 1 (mod ${n})`)];
      let ok = true; for (const [p] of factorSmall(k)) if (powModRL(a, k / p, n) === 1n) ok = false;
      cs.push(check("minimal", ok, `${a}^(${k}/p) ≢ 1 for every prime p dividing ${k}, so no smaller exponent works`));
      return cs;
    },
  };
}
// invariant factors of a finite abelian group given as a list of cyclic orders
function invariantFactors(orders) {
  const pp = new Map(); // prime -> exponents
  for (const o of orders) for (const [p, e] of factorSmall(o) || []) { if (!pp.has(p)) pp.set(p, []); pp.get(p).push(e); }
  const len = Math.max(0, ...[...pp.values()].map((v) => v.length));
  const inv = Array(len).fill(1n);
  for (const [p, es] of pp) { es.sort((a, b) => b - a); es.forEach((e, i) => { inv[len - 1 - i] *= p ** BigInt(e); }); }
  return inv.filter((d) => d > 1n);
}
const zText = (fs) => (fs.length ? fs.map((d) => `Z_${d}`).join(" × ") : "trivial group");
function unitStructure(n) {
  const cyc = [];
  for (const [p, e] of factorSmall(n)) {
    if (p === 2n) { if (e === 2) cyc.push(2n); else if (e >= 3) cyc.push(2n, 2n ** BigInt(e - 2)); }
    else cyc.push((p - 1n) * p ** BigInt(e - 1));
  }
  return invariantFactors(cyc);
}
function cmdUnitGroup(args) {
  const n = intOf(args[0]);
  if (n < 1n) throw refuse("n must be positive");
  if (n > 1000000n) throw refuse("U(n) is analysed for n up to 1,000,000");
  const ph = totient(n);
  const inv = unitStructure(n);
  const cyclic = inv.length <= 1;
  const answers = [ansNum("group order", ph), ansYes("cyclic", cyclic), ansText("structure", zText(inv))];
  let roots = [];
  if (cyclic) {
    for (let g = 1n; g < n || (n === 1n && g === 1n); g++) { if (gcd(g, n) === 1n && multOrder(g, n) === ph) roots.push(g); if (n === 1n) break; }
    if (n === 1n) roots = [0n];
    answers.push(roots.length <= 120 ? ansText("primitive roots", `{${roots.join(", ")}}`) : ansText("primitive roots", `${roots.length} primitive roots, the smallest is ${roots[0]}`));
    answers.push(ansNum("number of primitive roots", roots.length));
  } else answers.push(ansText("primitive roots", "none (U(n) is not cyclic)"));
  return {
    answers,
    steps: [step("group.units", `U(${n}) has φ(${n}) = ${ph} elements`, "The units mod n are the residues coprime to n."),
      step("group.units.structure", "Structure from the Chinese remainder theorem", `U(${n}) ≅ ${zText(inv)}; it is cyclic exactly when n is 1, 2, 4, p^k or 2p^k.`)],
    checks: () => {
      // brute force: element orders by repeated multiplication
      const units = []; for (let a = 1n; a <= n; a++) if (gcd(a, n) === 1n) units.push(a % n);
      const ord = units.map((a) => { let k = 1n, x = a % n; while (x !== 1n % n && k <= ph) { x = x * a % n; k++; } return k; });
      const cs = [check("count", BigInt(units.length) === ph, `${units.length} residues are coprime to ${n}`)];
      // order distribution of the claimed structure: #{x : x^d = 1} = prod gcd(d, n_i)
      const divs = []; for (let d = 1n; d <= ph; d++) if (ph % d === 0n) divs.push(d);
      const same = divs.every((d) => BigInt(ord.filter((k) => d % k === 0n).length) === inv.reduce((a, m) => a * gcd(d, m), 1n));
      cs.push(check("order distribution", same, `for every d | ${ph}, the number of units with x^d = 1 matches ${zText(inv)}`));
      if (cyclic) {
        const brute = units.filter((_, i) => ord[i] === ph).sort((a, b) => (a < b ? -1 : 1));
        cs.push(check("primitive roots", n === 1n || (brute.length === roots.length && brute.every((g, i) => g === roots[i])), `brute force finds the same ${brute.length} element(s) of order ${ph}`));
      } else cs.push(check("not cyclic", !ord.some((k) => k === ph), `no unit has order ${ph}`));
      return cs;
    },
  };
}
function divisors(n) { const out = []; for (let d = 1n; d * d <= n; d++) if (n % d === 0n) { out.push(d); if (d * d !== n) out.push(n / d); } return out.sort((a, b) => (a < b ? -1 : 1)); }
function cmdCyclicGroup(args) {
  const n = intOf(args[0]);
  if (n < 1n || n > 100000n) throw refuse("Z_n is analysed for 1 <= n <= 100000");
  const gens = []; for (let k = 0n; k < n; k++) if (gcd(k, n) === 1n) gens.push(k);
  if (n === 1n) gens.splice(0, gens.length, 0n);
  const ds = divisors(n);
  const subs = ds.map((d) => ({ order: d, gen: n / d }));
  return {
    answers: [ansText("generators", gens.length <= 200 ? `{${gens.join(", ")}}` : `${gens.length} generators`), ansNum("number of generators", gens.length), ansNum("number of subgroups", subs.length),
      ansText("subgroups", subs.map((s) => `⟨${s.gen % n}⟩ (order ${s.order})`).join(", "))],
    steps: [step("group.cyclic.gens", "k generates Z_n exactly when gcd(k, n) = 1", `There are φ(${n}) = ${gens.length} generators.`),
      step("group.cyclic.subs", "Z_n has exactly one subgroup of each order d dividing n, namely ⟨n/d⟩", `${n} has ${ds.length} divisors.`)],
    checks: () => {
      const cs = [];
      if (n <= 5000n) {
        const genBrute = []; for (let k = 0n; k < n; k++) { const seen = new Set(); let x = 0n; do { seen.add(x); x = (x + k) % n; } while (x !== 0n); if (BigInt(seen.size) === n) genBrute.push(k); }
        cs.push(check("closure", genBrute.length === gens.length && genBrute.every((g, i) => g === gens[i]), "generating ⟨k⟩ for every k finds the same generators"));
      } else cs.push(check("closure", false, "too large for the brute-force closure check"));
      if (n <= 16n) {
        let count = 0;
        for (let S = 1; S < 1 << Number(n); S++) { if (!(S & 1)) continue; let closed = true; for (let a = 0; a < Number(n) && closed; a++) if (S & (1 << a)) for (let b = 0; b < Number(n); b++) if (S & (1 << b) && !(S & (1 << ((a + b) % Number(n))))) { closed = false; break; } if (closed) count++; }
        cs.push(check("all subsets", count === subs.length, `testing all ${2 ** Number(n)} subsets for closure finds ${count} subgroups`));
      } else {
        const found = new Set(); for (let k = 0n; k < n; k++) found.add(String(n / gcd(k, n)));
        cs.push(check("cyclic subgroups", found.size === subs.length, `the subgroups ⟨k⟩ for k = 0..${n - 1n} have ${found.size} different orders (every subgroup of a cyclic group is cyclic)`));
      }
      return cs;
    },
  };
}
function partitions(e) { const out = []; const rec = (left, max, cur) => { if (!left) { out.push(cur.slice()); return; } for (let k = Math.min(left, max); k >= 1; k--) { cur.push(k); rec(left - k, k, cur); cur.pop(); } }; rec(e, e, []); return out; }
function cmdAbelian(args) {
  const n = intOf(args[0]);
  if (n < 1n) throw refuse("the order must be positive");
  const f = factorSmall(n);
  if (!f || n > 10n ** 15n) throw refuse("the order is too large to factor");
  let groups = [[]];
  for (const [p, e] of f) { const parts = partitions(e); groups = groups.flatMap((g) => parts.map((pt) => [...g, ...pt.map((k) => p ** BigInt(k))])); }
  const invs = groups.map((g) => invariantFactors(g));
  const count = invs.length;
  const listed = count <= 60;
  const answers = [ansNum("number of groups", count)];
  if (listed) answers.push(ansText("groups", invs.map(zText).join("; ")));
  return {
    answers,
    steps: [step("group.abelian", "Fundamental theorem of finite abelian groups", `${n} = ${f.map(([p, e]) => (e > 1 ? `${p}^${e}` : `${p}`)).join(" · ")}; each prime power p^e contributes one choice per partition of e.`),
      step("group.abelian.count", "Multiply the partition counts", `${f.map(([, e]) => partitions(e).length).join(" × ")} = ${count}.`)],
    checks: () => {
      if (n > 10n ** 9n) return [check("chains", false, "too large to enumerate divisor chains")];
      // invariant-factor chains d1 | d2 | ... | dk with d1 > 1 and product n, enumerated directly
      const ds = divisors(n).filter((d) => d > 1n);
      let chains = 0; let nodes = 0;
      const rec = (rest, prev) => { if (++nodes > 2e6) throw refuse("too many chains"); if (rest === 1n) { chains++; return; } for (const d of ds) { if (d > rest) break; if (rest % d === 0n && d % prev === 0n) { const after = rest / d; if (after === 1n || after % d === 0n || true) rec2(after, d); } } };
      // rec2 enforces that later factors are multiples of the current one
      const rec2 = (rest, prev) => { if (rest === 1n) { chains++; return; } for (const d of ds) { if (d > rest) break; if (rest % d === 0n && d % prev === 0n) rec2(rest / d, d); } };
      void rec;
      if (n === 1n) chains = 1; else rec2(n, 1n);
      const cs = [check("divisor chains", chains === count, `enumerating chains d1 | d2 | ... with product ${n} gives ${chains}`)];
      if (listed) cs.push(check("orders", invs.every((g) => g.reduce((a, b) => a * b, 1n) === n && g.every((d, i) => i === 0 || d % g[i - 1] === 0n)), "every listed group has order n and a valid invariant-factor chain"));
      return cs;
    },
  };
}

// ---------------------------------------------------------------- finite fields
function primeArg(u, what = "p") {
  const p = intOf(u, `a prime ${what}`);
  if (p < 2n || !isPrimeSmall(p)) throw refuse(`${p} is not prime`);
  if (p > 10n ** 12n) throw refuse("the prime is too large");
  return p;
}
function gfEval(u, p, m, x) {
  // m: monic modulus (or null for GF(p))
  const R = (a) => (m ? P.rem(P.red(a, p), m, p) : P.red(a, p));
  const go = (w) => {
    switch (w.k) {
      case "num": { const r = w.v; const d = modInv(mod(r.d, p), p); if (d === null) throw refuse(`${r.d} is 0 in GF(${p}), so the division is undefined`); return R([mod(r.n, p) * d]); }
      case "sym": if (m && w.name === x) return R([0n, 1n]); throw refuse(m ? `unexpected symbol ${w.name}` : `GF(${p}) has no variable; give a modulus polynomial for GF(${p}^k)`);
      case "add": return w.args.map(go).reduce((a, b) => P.add(a, b, p));
      case "mul": return w.args.map(go).reduce((a, b) => R(P.mul(a, b, p)), [1n]);
      case "pow": {
        const e = ratOf(w.args[1]); if (!e || e.d !== 1n) throw refuse("exponents must be integers");
        let b = go(w.args[0]); let k = e.n;
        if (k < 0n) { b = invElt(b); k = -k; }
        return m ? P.powmod(b, k, m, p) : (b.length ? [powMod(b[0], k, p)] : k === 0n ? [1n] : []);
      }
      case "fn": if ((w.name === "inv" || w.name === "inverse") && w.args.length === 1) return invElt(go(w.args[0])); break;
    }
    throw refuse("unsupported operation in finite-field arithmetic");
  };
  const invElt = (a) => {
    if (!a.length) throw refuse("0 has no inverse");
    if (!m) return [modInv(a[0], p)];
    const r = P.inverse(a, m, p);
    if (!r) throw refuse("the element is not invertible (it shares a factor with the modulus)");
    return r;
  };
  return go(u);
}
// independent route: companion-matrix representation of GF(p)[x]/(m)
function matEval(u, p, m, x) {
  const k = m ? P.deg(m) : 1;
  const I = () => Array.from({ length: k }, (_, i) => Array.from({ length: k }, (_, j) => (i === j ? 1n : 0n)));
  const mm = (A, B) => A.map((r) => B[0].map((_, j) => r.reduce((s, v, t) => (s + v * B[t][j]) % p, 0n)));
  const ma = (A, B) => A.map((r, i) => r.map((v, j) => (v + B[i][j]) % p));
  const sc = (A, c) => A.map((r) => r.map((v) => mod(v * c, p)));
  const C = Array.from({ length: k }, () => Array(k).fill(0n)); // multiplication by x
  if (m) { for (let i = 1; i < k; i++) C[i][i - 1] = 1n; for (let i = 0; i < k; i++) C[i][k - 1] = mod(-m[i], p); }
  const inv = (A) => { // Gauss-Jordan mod p
    const M = A.map((r, i) => [...r, ...I()[i]]);
    for (let c = 0; c < k; c++) {
      let r = c; while (r < k && M[r][c] === 0n) r++;
      if (r === k) throw refuse("singular");
      [M[c], M[r]] = [M[r], M[c]];
      const iv = powModRL(M[c][c], p - 2n, p);
      M[c] = M[c].map((v) => v * iv % p);
      for (let i = 0; i < k; i++) if (i !== c && M[i][c]) { const f = M[i][c]; M[i] = M[i].map((v, j) => mod(v - f * M[c][j], p)); }
    }
    return M.map((r) => r.slice(k));
  };
  const pw = (A, e) => { let R = I(), B = A; while (e > 0n) { if (e & 1n) R = mm(R, B); B = mm(B, B); e >>= 1n; } return R; };
  const go = (w) => {
    switch (w.k) {
      case "num": return sc(inv(sc(I(), mod(w.v.d, p))), mod(w.v.n, p));
      case "sym": return C;
      case "add": return w.args.map(go).reduce(ma);
      case "mul": return w.args.map(go).reduce(mm, I());
      case "pow": { const e = ratOf(w.args[1]).n; const b = go(w.args[0]); return e < 0n ? pw(inv(b), -e) : pw(b, e); }
      case "fn": return inv(go(w.args[0]));
    }
    throw new Error("unsupported");
  };
  const R = go(u);
  return P.trim(R.map((r) => r[0]));
}
function cmdGF(args) {
  if (args.length < 2 || args.length > 3) throw refuse("gfcalc(expression, p[, modulus])");
  const p = primeArg(args[1]);
  let m = null, x = "x";
  if (args[2]) {
    const syms = [...X.freeSymbols(args[2])];
    if (syms.length !== 1) throw refuse("the modulus must be a polynomial in one variable");
    x = syms[0];
    m = P.monic(P.red(intPolyOf(args[2], x), p), p);
    if (P.deg(m) < 1) throw refuse("the modulus must have degree at least 1");
    if (P.deg(m) > 32) throw refuse("the modulus degree is limited to 32");
  }
  const val = gfEval(args[0], p, m, x);
  const irreducible = m ? P.rabin(m, p) : true;
  const field = m ? (irreducible ? `GF(${p}^${P.deg(m)})` : `GF(${p})[${x}]/(${P.ptext(m, x)})`) : `GF(${p})`;
  const answers = [ansTree("result", P.ptree(val, x))];
  const steps = [step("gf.eval", `Compute in ${field}`, m ? `Multiply as polynomials with coefficients mod ${p}, reduce modulo ${P.ptext(m, x)}; inverses come from the extended Euclidean algorithm.` : `Work mod ${p}; a / b means a · b^(-1) with b^(-1) from the extended Euclidean algorithm.`)];
  if (m && !irreducible) steps.push(step("gf.notfield", "The modulus is reducible", "So this is a ring with zero divisors, not a field; the computation is still exact."));
  return {
    answers, steps,
    checks: () => {
      const alt = matEval(args[0], p, m, x);
      return [check(m ? "companion matrix" : "Fermat inverse", P.eq(alt, val), m ? "evaluating with multiplication-by-x matrices mod p gives the same element" : "recomputing with b^(p-2) for every inverse gives the same value")];
    },
  };
}
function polyModArg(u, p) {
  const syms = [...X.freeSymbols(u)];
  if (syms.length > 1) throw refuse("expected a polynomial in one variable");
  const x = syms[0] || "x";
  return { f: P.red(intPolyOf(u, x), p), x };
}
function factorText(fs, x) { return fs.map(({ poly, mult }) => `${P.ptext(poly, x)}${mult > 1 ? ` ^${mult}` : ""}`).join(" ; "); }
function cmdFactorMod(args) {
  if (args.length !== 2) throw refuse("factormod(f, p)");
  const p = primeArg(args[1]);
  const { f, x } = polyModArg(args[0], p);
  if (P.deg(f) < 1) throw refuse(`the polynomial is constant mod ${p}`);
  if (P.deg(f) > 40) throw refuse("degree is limited to 40");
  const r = P.factorTrial(f, p);
  const answers = [ansText("irreducible factors", factorText(r.factors, x))];
  if (r.lc !== 1n) answers.push(ansNum("leading coefficient", r.lc));
  const pretty = r.factors.map(({ poly, mult }) => `(${P.ptext(poly, x)})${mult > 1 ? `^${mult}` : ""}`).join("");
  answers.push(ansText("factorization", `${r.lc !== 1n ? r.lc : ""}${pretty}`));
  return {
    answers,
    steps: [step("gf.factor", `Trial division by monic polynomials over GF(${p}) of increasing degree`, "Each divisor found is irreducible, because every smaller-degree factor has already been removed."), step("gf.factor.result", "Factorization", `${pretty} (mod ${p})`)],
    checks: () => {
      let prod = [r.lc];
      for (const { poly, mult } of r.factors) for (let i = 0; i < mult; i++) prod = P.mul(prod, poly, p);
      return [check("product", P.eq(prod, f), `multiplying the factors back gives the original polynomial mod ${p}`),
        check("Rabin test", r.factors.every(({ poly }) => P.rabin(poly, p)), "each factor passes Rabin's irreducibility test (x^(p^n) ≡ x and the gcd conditions)")];
    },
  };
}
function zPolyText(z, x = "x") { return P.ptext(z.map(BigInt), x); }
function eisenstein(z) {
  const n = z.length - 1, c = z.slice(0, n).reduce((g, v) => gcd(g, v), 0n);
  for (const [p] of factorSmall(c) || []) if (z[n] % p !== 0n && z[0] % (p * p) !== 0n) return p;
  return null;
}
function rationalRoots(z) { // candidate p/q with p | a0, q | an
  if (z[0] === 0n) return [N.ZERO];
  if (babs(z[0]) > 10n ** 12n || babs(z[z.length - 1]) > 10n ** 12n) return [null];
  const ps = divisors(babs(z[0])), qs = divisors(babs(z[z.length - 1]));
  const out = [];
  for (const a of ps) for (const b of qs) for (const s of [1n, -1n]) { const r = N.Q(s * a, b); let v = N.ZERO; for (let i = z.length - 1; i >= 0; i--) v = N.add(N.mul(v, r), N.Q(z[i])); if (N.isZero(v)) out.push(r); }
  return out;
}
function irreducibleOverQ(u) {
  const syms = [...X.freeSymbols(u)];
  if (syms.length > 1) throw refuse("expected a polynomial in one variable");
  const x = syms[0] || "x";
  const q = polyOf(u, x);
  if (q.length < 2) throw refuse("constants are not irreducible polynomials");
  const L = q.reduce((a, c) => lcm(a, c.d), 1n);
  const z = q.map((c) => c.n * (L / c.d));
  if (z.length > 30) throw refuse("degree is limited to 29");
  const r = factorZ(z);
  if (!r.verified) throw refuse("the factorization could not be verified");
  const nontrivial = r.factors.filter((f) => f.poly.length > 1);
  const irr = nontrivial.length === 1 && nontrivial[0].mult === 1;
  return { z, x, r, irr };
}
function cmdIrreducible(args) {
  if (args.length < 1 || args.length > 2) throw refuse("isirreducible(f, p) with p = 0 for Q");
  const pp = args[1] ? intOf(args[1]) : 0n;
  if (pp === 0n) {
    const { z, x, r, irr } = irreducibleOverQ(args[0]);
    const n = z.length - 1;
    const fs = r.factors.map(({ poly, mult }) => `(${zPolyText(poly, x)})${mult > 1 ? `^${mult}` : ""}`).join("");
    return {
      answers: [ansYes("irreducible", irr), ...(irr ? [] : [ansText("factorization", `${r.unit !== 1n ? r.unit : ""}${fs}`)])],
      steps: [step("poly.irrQ", "Factor over the integers (Zassenhaus)", irr ? "No factorization into lower-degree polynomials exists." : `It factors as ${fs}.`)],
      checks: () => {
        if (!irr) {
          let prod = [r.unit]; for (const { poly, mult } of r.factors) for (let i = 0; i < mult; i++) prod = zmul(prod, poly);
          return [check("factors multiply back", zeq(prod, z) && r.factors.some((f) => f.poly.length > 1 && f.poly.length - 1 < n), "the factors have lower degree and their product is the polynomial")];
        }
        if (n === 1) return [check("degree 1", true, "every polynomial of degree 1 is irreducible")];
        const ep = eisenstein(z);
        if (ep) return [check("Eisenstein", true, `Eisenstein's criterion applies at p = ${ep}`)];
        if (n <= 3 && rationalRoots(z).length === 0) return [check("rational root test", true, `a polynomial of degree ${n} with no rational root (all candidates p/q tested) has no linear factor, so it is irreducible`)];
        const content = z.reduce((g, v) => gcd(g, v), 0n);
        const prim = z.map((v) => v / content);
        for (let p = 2n; p < 2000n; p++) {
          if (!isPrimeSmall(p) || prim[n] % p === 0n) continue;
          const fp = P.red(prim, p);
          if (P.deg(fp) === n && P.rabin(fp, p)) return [check("irreducible mod p", true, `modulo ${p} the polynomial keeps its degree and is irreducible (Rabin's test), so it is irreducible over Q`)];
        }
        return [check("certificate", false, "no independent certificate of irreducibility was found")];
      },
    };
  }
  const p = primeArg(args[1]);
  const { f, x } = polyModArg(args[0], p);
  if (P.deg(f) < 1) throw refuse(`the polynomial is constant mod ${p}`);
  const irr = P.rabin(f, p);
  return {
    answers: [ansYes("irreducible", irr)],
    steps: [step("gf.rabin", `Rabin's test over GF(${p})`, `f has degree ${P.deg(f)}; f is irreducible iff x^(p^n) ≡ x (mod f) and gcd(x^(p^(n/q)) - x, f) = 1 for each prime q | n.`)],
    checks: () => {
      const r = P.factorTrial(f, p);
      const single = r.factors.length === 1 && r.factors[0].mult === 1;
      return [check("trial division", single === irr, single ? "trial division finds no factor of degree <= n/2" : `trial division finds the factorization ${factorText(r.factors, x)}`)];
    },
  };
}
const zmul = (a, b) => { const r = Array(a.length + b.length - 1).fill(0n); a.forEach((u, i) => b.forEach((v, j) => { r[i + j] += u * v; })); return r; };
const zeq = (a, b) => { const t = (c) => { const r = c.map(BigInt); while (r.length && r[r.length - 1] === 0n) r.pop(); return r; }; const A = t(a), B = t(b); return A.length === B.length && A.every((v, i) => v === B[i]); };

// ---------------------------------------------------------------- quotient rings
function cmdQuotient(args) {
  if (args.length < 1 || args.length > 2) throw refuse("quotientring(f[, p])");
  if (args[1]) {
    const p = primeArg(args[1]);
    const { f, x } = polyModArg(args[0], p);
    if (P.deg(f) < 1) throw refuse(`the polynomial is constant mod ${p}`);
    const irr = P.rabin(f, p);
    const size = p ** BigInt(P.deg(f));
    const r = irr ? null : P.factorTrial(f, p);
    const answers = [ansYes("field", irr), ansYes("integral domain", irr), ansNum("number of elements", size)];
    let zd = null;
    if (!irr) {
      const g = r.factors[0].poly; const h = P.divmod(P.monic(f, p), g, p)[0];
      zd = [g, h];
      answers.push(ansText("zero divisors", `(${P.ptext(g, x)})·(${P.ptext(h, x)}) = 0`));
    }
    return {
      answers,
      steps: [step("ring.quotient", `Z_${p}[${x}]/(${P.ptext(f, x)}) is a field exactly when the modulus is irreducible over GF(${p})`, irr ? "It is irreducible (Rabin's test)." : "It factors, so the factors are zero divisors."), step("ring.size", "Size", `${p}^${P.deg(f)} = ${size} elements.`)],
      checks: () => {
        if (irr) { const t = P.factorTrial(f, p); return [check("trial division", t.factors.length === 1 && t.factors[0].mult === 1, "trial division finds no proper factor")]; }
        const prod = P.mul(zd[0], zd[1], p);
        return [check("zero divisors", P.deg(zd[0]) >= 1 && P.deg(zd[1]) >= 1 && P.deg(zd[0]) < P.deg(f) && P.deg(zd[1]) < P.deg(f) && P.rem(prod, f, p).length === 0, "two nonzero classes multiply to 0 in the quotient")];
      },
    };
  }
  // over Z
  const { z, x, r, irr } = irreducibleOverQ(args[0]);
  const content = z.reduce((g, v) => gcd(g, v), 0n);
  const domain = irr && content === 1n;
  return {
    answers: [ansYes("field", false), ansYes("integral domain", domain)],
    steps: [step("ring.quotientZ", `Z[${x}]/(${zPolyText(z, x)})`, `It is an integral domain exactly when the polynomial is prime in Z[${x}] (primitive and irreducible). It is never a field: 2 has no inverse (the ring is a free Z-module of rank ${z.length - 1} when the polynomial is monic, and in general (f) is not a maximal ideal).`)],
    checks: () => {
      const cs = [];
      // not a field: a prime q not dividing the leading coefficient is a nonzero non-unit, since
      // Z[x]/(f, q) = Z_q[x]/(f mod q) is a nonzero ring when f mod q keeps degree >= 1
      let q = 2n; while (z[z.length - 1] % q === 0n) { q++; while (!isPrimeSmall(q)) q++; }
      const fq = P.red(z, q);
      cs.push(check("non-unit", P.deg(fq) >= 1, `${q} is not invertible: modulo ${q} the ring becomes Z_${q}[${x}]/(${P.ptext(fq, x)}), which is not zero, so the quotient is not a field`));
      if (domain) {
        const n = z.length - 1;
        let cert = n === 1 || !!eisenstein(z) || (n <= 3 && rationalRoots(z).length === 0);
        for (let p = 2n; !cert && p < 2000n; p++) if (isPrimeSmall(p) && z[n] % p !== 0n && P.rabin(P.red(z, p), p)) cert = true;
        cs.push(check("irreducible", cert, "an independent irreducibility certificate (degree 1, Eisenstein, rational roots, or irreducible mod p) exists"));
      } else {
        cs.push(check("reducible", !irr || content !== 1n, content !== 1n ? `the content ${content} is a zero divisor` : "the polynomial factors, giving zero divisors"));
      }
      void r;
      return cs;
    },
  };
}

// ---------------------------------------------------------------- Gaussian integers
function gOf(u) {
  switch (u.k) {
    case "num": if (u.v.d !== 1n) throw refuse("Gaussian integers have integer parts"); return [u.v.n, 0n];
    case "const": if (u.name === "I") return [0n, 1n]; break;
    case "add": return u.args.map(gOf).reduce((a, b) => [a[0] + b[0], a[1] + b[1]]);
    case "mul": return u.args.map(gOf).reduce(gmul, [1n, 0n]);
    case "pow": { const e = ratOf(u.args[1]); if (!e || e.d !== 1n || e.n < 0n || e.n > 64n) break; let r = [1n, 0n]; const b = gOf(u.args[0]); for (let i = 0n; i < e.n; i++) r = gmul(r, b); return r; }
  }
  throw refuse("expected a Gaussian integer a + b i");
}
const gmul = (a, b) => [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]];
const gsub = (a, b) => [a[0] - b[0], a[1] - b[1]];
const gnorm = (a) => a[0] * a[0] + a[1] * a[1];
const rdiv = (a, b) => { const q = a / b, r = a - q * b; return 2n * babs(r) > babs(b) ? q + ((r > 0n) === (b > 0n) ? 1n : -1n) : q; };
function gdivmod(a, b) { const n = gnorm(b); const t = gmul(a, [b[0], -b[1]]); const q = [rdiv(t[0], n), rdiv(t[1], n)]; return [q, gsub(a, gmul(q, b))]; }
function gdivExact(a, b) { const n = gnorm(b); const t = gmul(a, [b[0], -b[1]]); if (t[0] % n !== 0n || t[1] % n !== 0n) return null; return [t[0] / n, t[1] / n]; }
const UNITS = [[1n, 0n], [0n, 1n], [-1n, 0n], [0n, -1n]];
function gnormalise(a) { if (!a[0] && !a[1]) return { z: a, u: [1n, 0n] }; for (const u of UNITS) { const z = gmul(a, u); if (z[0] > 0n && z[1] >= 0n) return { z, u }; } throw new Error("unreachable"); }
const gtree = (a) => simplify(X.add(X.num(a[0]), X.mul(X.num(a[1]), X.I)));
const gtext = (a) => (a[1] === 0n ? `${a[0]}` : a[0] === 0n ? `${a[1] === 1n ? "" : a[1] === -1n ? "-" : a[1]}i` : `${a[0]} ${a[1] < 0n ? "-" : "+"} ${babs(a[1]) === 1n ? "" : babs(a[1])}i`);
function cmdGaussGcd(args) {
  if (args.length !== 2) throw refuse("gaussgcd(a, b)");
  const a = gOf(args[0]), b = gOf(args[1]);
  if (!gnorm(a) && !gnorm(b)) throw refuse("gcd(0, 0) is not defined");
  // extended Euclid
  let [r0, r1, s0, s1, t0, t1] = [a, b, [1n, 0n], [0n, 0n], [0n, 0n], [1n, 0n]];
  const trace = [];
  while (gnorm(r1)) { const [q, r] = gdivmod(r0, r1); trace.push(`${gtext(r0)} = (${gtext(q)})(${gtext(r1)}) + ${gtext(r)}`); [r0, r1] = [r1, r]; [s0, s1] = [s1, gsub(s0, gmul(q, s1))]; [t0, t1] = [t1, gsub(t0, gmul(q, t1))]; }
  const { z: g, u } = gnormalise(r0);
  const x = gmul(s0, u), y = gmul(t0, u);
  return {
    answers: [ansTree("gcd", gtree(g)), ansNum("norm", gnorm(g)), ansText("bezout", `(${gtext(a)})(${gtext(x)}) + (${gtext(b)})(${gtext(y)}) = ${gtext(g)}`)],
    steps: [step("gauss.euclid", "Euclidean algorithm in Z[i] (divide, round the quotient to the nearest Gaussian integer)", trace.slice(0, 12).join("; ")), step("gauss.normalise", "Normalise by a unit so that the real part is positive and the imaginary part is non-negative", `gcd = ${gtext(g)}`)],
    checks: () => {
      const comb = gsub(gmul(a, x), gmul(b, [-y[0], -y[1]]));
      const divA = gdivExact(a, g), divB = gdivExact(b, g);
      return [check("common divisor", !!divA && !!divB, `${gtext(g)} divides both numbers exactly`), check("Bezout", comb[0] === g[0] && comb[1] === g[1], `a·x + b·y = ${gtext(g)}, so every common divisor divides it`)];
    },
  };
}
function twoSquares(p) { for (let a = 1n; a * a <= p; a++) { const b2 = p - a * a; let b = BigInt(Math.round(Math.sqrt(Number(b2)))); while (b * b > b2) b--; while ((b + 1n) * (b + 1n) <= b2) b++; if (b * b === b2 && b > 0n) return [a, b]; } return null; }
function cmdGaussFactor(args) {
  if (args.length !== 1) throw refuse("gaussfactor(z)");
  const z0 = gOf(args[0]);
  const n = gnorm(z0);
  if (n === 0n) throw refuse("0 has no factorization");
  if (n === 1n) throw refuse(`${gtext(z0)} is a unit`);
  if (n > 10n ** 14n) throw refuse("the norm is too large to factor");
  let z = z0; const fs = [];
  for (const [p, e] of factorSmall(n)) {
    if (p === 2n) { for (let i = 0; i < e; i++) { const q = gdivExact(z, [1n, 1n]); z = q; fs.push([1n, 1n]); } continue; }
    if (p % 4n === 3n) { for (let i = 0; i < e / 2; i++) { z = gdivExact(z, [p, 0n]); fs.push([p, 0n]); } continue; }
    const [a, b] = twoSquares(p);
    const pis = [[a, b], [a, -b]].map((w) => gnormalise(w).z);
    let left = e;
    for (const pi of pis) { for (;;) { if (!left) break; const q = gdivExact(z, pi); if (!q) break; z = q; fs.push(pi); left--; } }
    if (left) throw refuse("internal factorization mismatch");
  }
  const unit = z;
  fs.sort((u, v) => { const d = gnorm(u) - gnorm(v); return d ? (d < 0n ? -1 : 1) : u[0] !== v[0] ? (u[0] < v[0] ? -1 : 1) : u[1] < v[1] ? -1 : 1; });
  const text = `${unit[0] === 1n && unit[1] === 0n ? "" : `${gtext(unit)} · `}${fs.map((f) => `(${gtext(f)})`).join("")}`;
  return {
    answers: [ansText("factorization", text), ansText("norms", fs.map(gnorm).join(", ")), ansText("unit", gtext(unit))],
    steps: [step("gauss.norm", `N(${gtext(z0)}) = ${n}`, "Each Gaussian prime factor has norm 2, a prime p ≡ 1 (mod 4), or p^2 for a prime p ≡ 3 (mod 4)."),
      step("gauss.split", "Split each rational prime", "2 = -i(1 + i)^2; p ≡ 1 (mod 4) is (a + bi)(a - bi) with a^2 + b^2 = p; p ≡ 3 (mod 4) stays prime."), step("gauss.result", "Factorization", text)],
    checks: () => {
      let prod = unit; for (const f of fs) prod = gmul(prod, f);
      const primes = fs.every((f) => { const m = gnorm(f); if (isPrimeSmall(m)) return true; const r = BigInt(Math.round(Math.sqrt(Number(m)))); return r * r === m && isPrimeSmall(r) && r % 4n === 3n && f[1] === 0n; });
      return [check("product", prod[0] === z0[0] && prod[1] === z0[1] && UNITS.some((u) => u[0] === unit[0] && u[1] === unit[1]), "the unit times the factors gives the original number"), check("primes", primes, "every factor has prime norm or is a rational prime ≡ 3 (mod 4)")];
    },
  };
}

export const ALGEBRA_HANDLERS = {
  perminfo: cmdPermInfo, permcompose: cmdPermCompose, elementorder: cmdElementOrder, unitgroup: cmdUnitGroup, cyclicgroup: cmdCyclicGroup, abeliangroups: cmdAbelian,
  gfcalc: cmdGF, factormod: cmdFactorMod, isirreducible: cmdIrreducible, gaussgcd: cmdGaussGcd, gaussfactor: cmdGaussFactor, quotientring: cmdQuotient,
};
