# Quelvra

An offline math engine that shows an answer only after checking it independently.
If it cannot prove an answer, it says so instead of guessing.

Live: [darknode.ai/quelvra](https://darknode.ai/quelvra/)

## What it does

- **Algebra:** simplify, expand, factor, rationalise, and solve equations, inequalities and systems.
- **Calculus:** derivatives, integrals (definite and indefinite), limits, series, and differential equations.
- **Function analysis:** domain, range, zeros, asymptotes, extrema, inflection points, tangent lines, inverses, and area and volume.
- **Linear algebra:** determinants, inverses, eigenvalues, row reduction, and dot and cross products.
- **Number theory:** primality proofs with certificates, factoring, congruences, and the Chinese remainder theorem.
- **Units:** conversions with exact factors, e.g. "60 miles per hour to meters per second".
- **Open problems:** bounded explorations (Collatz, Goldbach, twin primes, zeta zeros) that never claim a proof.
- **Input:** typed math, LaTeX, Unicode, plain English, handwriting, or a photo.
- **Modes:** Answer, Steps and Teach, plus "Check my work", which finds the first wrong line.

Every result carries a four-part confidence: recognition, classification, solution and verification.
The verifier uses its own numerics, separate from the solver's.

## Layout

| Path | Contents |
|---|---|
| `public/` | The site: `index.html`, UI, web worker, and service worker (offline) |
| `public/engine/` | The math engine (plain ES modules, no dependencies) |
| `test/` | Test suite (`npm test`) and benchmark (`npm run bench`) |
| `tools/sw-files.mjs` | Regenerates the service worker's offline file list |

## Develop

```
npm test            # full test suite
npm run bench       # benchmark: counts only verified-correct answers
npm run serve       # http://127.0.0.1:8080
```

Node 20 or newer. There is nothing to install.

## Deploy on Render

This is a **Static Site** on Render: no server, since all math runs in the browser. `render.yaml` sets it up.

- Build command: `node tools/sw-files.mjs`
- Publish directory: `public`
- Rewrite: `/*` to `/index.html`

The page only runs on allowed hostnames (see the first script in `public/index.html`).
Add the Render hostname there before the first deploy.

## License

Source-available, see [LICENSE](LICENSE). Copyright (c) 2026 SpartanKing18 (Manav Jawahar).
