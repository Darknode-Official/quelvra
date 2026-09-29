// Quelvra offline service worker. Scope: the folder it is served from.
// Precaches every Quelvra file and serves /quelvra/ GET requests network-first, falling back
// to the cache when offline, so a deploy is never masked by stale engine modules. Every
// successful response refreshes the cache. Requests outside /quelvra/ are never intercepted.
// FILES and VERSION are generated: run `node tools/quelvra-sw-files.mjs` before deploying.

const VERSION = "quelvra-mum639jt";
const BASE = new URL("./", self.location).pathname; // "/" on its own site, "/quelvra/" on darknode.ai
const FILES = [
  "",
  "app.css",
  "app.js",
  "bridge-shared.js",
  "bridge.js",
  "engine/advanced/complex.js",
  "engine/advanced/curves.js",
  "engine/advanced/language-patterns.js",
  "engine/advanced/multint.js",
  "engine/advanced/multivar.js",
  "engine/advanced/names.js",
  "engine/advanced/numerical.js",
  "engine/advanced/pde.js",
  "engine/advanced/transforms.js",
  "engine/advanced/util.js",
  "engine/advanced/vector.js",
  "engine/analysis/core.js",
  "engine/analysis/domainset.js",
  "engine/analysis/features.js",
  "engine/analysis/inverse.js",
  "engine/analysis/misc.js",
  "engine/analysis/util.js",
  "engine/bigfloat.js",
  "engine/calc/cutil.js",
  "engine/calc/diff.js",
  "engine/calc/int-definite.js",
  "engine/calc/int-limit.js",
  "engine/calc/int-norman.js",
  "engine/calc/int-rational.js",
  "engine/calc/int-special.js",
  "engine/calc/int-util.js",
  "engine/calc/integrate.js",
  "engine/calc/limit-steps.js",
  "engine/calc/limit.js",
  "engine/calc/ode.js",
  "engine/calc/recur.js",
  "engine/calc/series.js",
  "engine/calc/sum.js",
  "engine/discrete.js",
  "engine/discrete/algebra.js",
  "engine/discrete/crypto.js",
  "engine/discrete/decode.js",
  "engine/discrete/gfpoly.js",
  "engine/discrete/graph.js",
  "engine/discrete/lang-algebra.js",
  "engine/discrete/lang-crypto.js",
  "engine/discrete/lang-graph.js",
  "engine/discrete/lang-logic.js",
  "engine/discrete/lang-lp.js",
  "engine/discrete/lang-proof.js",
  "engine/discrete/lang-seq.js",
  "engine/discrete/lang-sets.js",
  "engine/discrete/lang-topology.js",
  "engine/discrete/lang-util.js",
  "engine/discrete/lang.js",
  "engine/discrete/logic.js",
  "engine/discrete/lp.js",
  "engine/discrete/names.js",
  "engine/discrete/proof.js",
  "engine/discrete/sequences.js",
  "engine/discrete/sets.js",
  "engine/discrete/topology.js",
  "engine/discrete/util.js",
  "engine/domain.js",
  "engine/explain.js",
  "engine/expr.js",
  "engine/identify.js",
  "engine/interval.js",
  "engine/language-more.js",
  "engine/language-words.js",
  "engine/language.js",
  "engine/linalg.js",
  "engine/logic.js",
  "engine/mistakes.js",
  "engine/num.js",
  "engine/numeric.js",
  "engine/numtheory.js",
  "engine/orchestrate.js",
  "engine/parse.js",
  "engine/poly-apart.js",
  "engine/poly-core.js",
  "engine/poly-factor.js",
  "engine/poly-roots.js",
  "engine/poly.js",
  "engine/primeproof.js",
  "engine/print.js",
  "engine/quelvra.js",
  "engine/research/bricks.js",
  "engine/research/budget.js",
  "engine/research/cards.js",
  "engine/research/collatz.js",
  "engine/research/kaprekar.js",
  "engine/research/primes.js",
  "engine/research/sofa.js",
  "engine/research/zeta.js",
  "engine/rules.js",
  "engine/simplify.js",
  "engine/solve/core.js",
  "engine/solve/equation.js",
  "engine/solve/groebner.js",
  "engine/solve/inequality.js",
  "engine/solve/integer.js",
  "engine/solve/lambert.js",
  "engine/solve/lambertw.js",
  "engine/solve/numeric.js",
  "engine/solve/optimize.js",
  "engine/solve/poly.js",
  "engine/solve/system.js",
  "engine/solve/trig.js",
  "engine/solve/util.js",
  "engine/specfun.js",
  "engine/stats.js",
  "engine/steps.js",
  "engine/strategies/advanced-continuous.js",
  "engine/strategies/advanced-discrete.js",
  "engine/strategies/analysis.js",
  "engine/strategies/basic.js",
  "engine/strategies/calculus.js",
  "engine/strategies/compute-more.js",
  "engine/strategies/compute.js",
  "engine/strategies/integrate.js",
  "engine/strategies/research.js",
  "engine/strategies/solve.js",
  "engine/units.js",
  "engine/verify-discrete.js",
  "engine/verify.js",
  "engine/vision/glyphs.js",
  "engine/vision/index.js",
  "engine/vision/layout.js",
  "engine/vision/photo.js",
  "engine/vision/raster.js",
  "engine/vision/strokes.js",
  "graph.js",
  "icon.svg",
  "index.html",
  "ink.js",
  "manifest.webmanifest",
  "mathml.js",
  "storage.js",
  "tools-core.js",
  "tools.js",
  "worker.js",
].map((f) => BASE + f);

self.addEventListener("install", (event) => {
  event.waitUntil(
    caches.open(VERSION).then(async (cache) => {
      // add individually so one missing optional file cannot break installation
      await Promise.all(FILES.map((url) => cache.add(new Request(url, { cache: "reload" })).catch(() => null)));
    }).then(() => self.skipWaiting())
  );
});

self.addEventListener("activate", (event) => {
  event.waitUntil(
    caches.keys()
      .then((keys) => Promise.all(keys.filter((k) => k.startsWith("quelvra-") && k !== VERSION).map((k) => caches.delete(k))))
      .then(() => self.clients.claim())
  );
});

function inScope(url) {
  return url.origin === self.location.origin && url.pathname.startsWith(BASE);
}

self.addEventListener("fetch", (event) => {
  const req = event.request;
  if (req.method !== "GET") return;
  const url = new URL(req.url);
  if (!inScope(url)) return;
  const key = url.pathname === BASE || url.pathname === BASE + "index.html" ? BASE + "index.html" : url.pathname;
  event.respondWith(
    caches.open(VERSION).then(async (cache) => {
      const res = await fetch(req, { cache: "no-cache" }).catch(() => null);
      if (res && res.ok && res.type === "basic") {
        cache.put(key, res.clone()).catch(() => null);
        return res;
      }
      const cached = await cache.match(key, { ignoreSearch: true });
      if (cached) return cached;
      if (res) return res;
      if (req.mode === "navigate") {
        const shell = await cache.match(BASE + "index.html");
        if (shell) return shell;
      }
      return new Response("Offline and not cached", { status: 503, headers: { "Content-Type": "text/plain" } });
    })
  );
});
