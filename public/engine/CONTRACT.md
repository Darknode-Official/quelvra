# Quelvra engine contract

Quelvra is an offline, deterministic computer algebra system. Neural parts may READ math;
only the deterministic algorithms in this directory SOLVE it. No network access, no CDN,
no eval / new Function, no JavaScript Number for exact mathematics.

All modules are plain ES modules that run unchanged in Node 20 (tests) and in browsers
(Web Worker). No npm dependencies. No DOM access inside `engine/`.

## Foundation (owned by the lead; do not edit, report bugs instead)

| File | Provides |
| --- | --- |
| `num.js` | Exact rationals on BigInt: `Q(n,d)`, `add sub mul div neg inv pow abs cmp eq floor ceil`, `iroot(n,k)`, `trialFactor`, `extractPower`, `fromDecimal`, `toDecimalString`, `toFloat` (approximations only), `factorial`, `binom`, `bgcd` |
| `expr.js` | The math tree. Immutable hash-consed nodes (`a === b` is structural equality). Constructors (raw, NOT simplified): `num sym konst add mul pow neg sub div recip sqrt exp fn eq rel and or not system tuple vector matrix set interval piecewise deriv integral limit sum product fndef quant`. Constants `ZERO ONE TWO NEG_ONE HALF PI E I OO UNDEF TRUE FALSE`. Helpers `withArgs mapTree freeSymbols hasSym freeOf contains subs replace size depth before sortArgs coeffAndTerm baseExp isNum isInt isZero isOne isSym isConst isFn` |
| `simplify.js` | `simplify(u, ctx)` automatic canonicaliser; `S.add/sub/mul/div/pow/neg/sqrt/fn/num` simplifying builders; `expand(u)`, `together(u)`, `numerDenom(u)`; `simpAdd simpMul simpPow simpFn`; `makeCtx({domain, assume, conditions, budget})`; `isReal(u)`, `signOf(u)` |
| `parse.js` | `parse(src)`, `parseDetailed(src) -> {node, warnings}`, `QuelvraSyntaxError {pos, hint}`, `latexToText` |
| `print.js` | `toText(u)` (re-parseable), `toLatex(u)` |

### Canonical form facts you can rely on
* Numbers are exact `num` nodes (`u.v` is a Rational `{n, d}` of BigInt). Decimals typed by the user are exact rationals.
* `a - b` is `add(a, mul(-1, b))`; `a / b` is `mul(a, pow(b, -1))`; `sqrt(u)` is `pow(u, 1/2)`; `e^x` is `pow(E, x)`; `log(b, x)` is `fn("log", b, x)`; `ln(x)` is `fn("ln", x)`; `|x|` is `fn("abs", x)`.
* After `simplify`: sums/products are flat and sorted; the numeric coefficient of a product is its FIRST arg; like terms and like bases are merged; nothing is expanded.
* `sqrt(x^2) -> |x|` in the real domain. `x/x -> 1` is performed but the condition `x != 0` is pushed to `ctx.conditions` when the caller passes `makeCtx({conditions: []})`.
* Default domain is `"real"`: symbols are real, odd roots of negatives are real (`(-8)^(1/3) = -2`), even roots of negatives give `I` multiples, `ln` of a negative number is `UNDEF`.
* `UNDEF` propagates. `OO` is +infinity; `-oo` is `mul(-1, OO)`.
* Budgets: `simplify` throws `{code: "BUDGET"}` when `ctx.budget.ops` is exhausted. Every loop you write must also be bounded; throw an Error with `code: "BUDGET"` or `code: "TIMEOUT"` rather than hanging.

## Numbers you return
Exact results are trees. Approximate results are NEVER silently mixed into trees; they are
returned as an `Approx` record:

```
{ value: "1.41421356237309504880", digits: 20, requested: 20,
  errorBound: "1e-21" | null, method: "brent", iterations: 12, converged: true }
```

## Step records
Every transformation that a user could see is recorded:

```
{ rule: "quadratic.formula",          // stable identifier
  title: "Apply the quadratic formula", // short human title
  why: "The equation has the form ax^2 + bx + c = 0 with a = 1, b = -5, c = 6.",
  before: node, after: node,            // trees (the explainer prints them)
  conditions: [node],                   // e.g. rel("!=", x, 0) that must hold
  sub: [StepRecord],                    // optional sub-steps
  kind: "equivalent" | "conditional" | "approximation" }
```
Produce steps with `makeStep(...)` from `steps.js` once it exists; until then plain objects of this shape.

## Solver result (what the orchestrator returns and the UI renders)

```
{ ok, input: {text, tree, warnings}, recognition: {source, confidence},
  classification: {kind, family, unknowns, domain, goal, method},
  answers: [{ kind: "exact" | "approx" | "set" | "interval" | "none", tree?, approx?, label? }],
  solutionStatus: "exact" | "approximate" | "partial" | "unsolved" | "unsupported",
  verification: { status: "passed" | "failed" | "partial" | "not-applicable",
                  checks: [{ name, method, passed, detail }] },
  steps: [StepRecord], conditions: [node], rejected: [{ value: node, reason }],
  attempts: [{ strategy, status: "ok" | "failed" | "skipped", reason, ms }],
  graph: { exprs: [node], marks: [{ x, y, label, kind }] } | null, ms }
```

## Tests
Tests live in `darknode-web/test/quelvra/*.test.js`, run with `node test/quelvra/run.js`
(optionally `node test/quelvra/run.js poly` to filter by file name). Use the harness in
`test/quelvra/harness.js`: `test(name, fn)`, `eq(actual, expected, msg)`, `ok(cond, msg)`,
`throws(fn)`, `T(src)` (parse+simplify+toText), `rng(seed)` for property tests.
Every module ships with unit tests AND property tests where a mathematical law exists.

## Answer shapes by problem kind (the benchmark and UI rely on these)
* Value / expression / derivative / definite integral / limit / sum: `{ kind: "exact", tree }` plus optionally `{ kind: "approx", approx }`.
  Limits that do not exist: `{ kind: "none", label: "The limit does not exist", reason }` with `solutionStatus: "exact"` (it is a proven fact). Infinite limits return `tree: OO` or `-OO`.
* Antiderivative: `{ kind: "exact", tree: F, constant: true }` (the UI prints "+ C").
* Equation in one unknown: one answer per solution `{ kind: "exact", label: "x", tree }` or `{ kind: "approx", label: "x", approx }`.
  Proven empty solution set: `answers: [{ kind: "none", label: "No real solution", proof: "..." }]`, `solutionStatus: "exact"`, `noSolution: true` on the result.
  Every real number: `{ kind: "all", label: "x", tree: TRUE }` (identity), with any excluded points listed in `conditions`.
  Periodic (trig) families: `{ kind: "general", label: "x", tree, param: "k" }` where `tree` contains the free symbol k (an integer), e.g. `pi/6 + 2 k pi`.
* Inequality: `{ kind: "set", label: "x", tree }` where tree is a relation / and / or in x (e.g. `or(rel("<", x, -2), rel(">", x, 2))`), or `FALSE` for no solution, `TRUE` for all reals. Also `interval: [{lo, hi, loOpen, hiOpen}]` for the UI.
* System: one answer per solution `{ kind: "solution", values: [["x", tree], ["y", tree]] }`; proven inconsistent: `{ kind: "none" }` + `noSolution: true`; infinitely many: `{ kind: "family", values: [...], params: ["t"] }`.
* Refusal / unsupported: `ok: false` or `answers: [{ kind: "none", label: reason }]` with `solutionStatus: "unsupported" | "unsolved"`.
