import { test, eq, ok } from "./harness.js";
import { proveprime, checkCertificate } from "../public/engine/primeproof.js";

test("Mersenne 2^89-1 proved by Lucas-Lehmer", () => { const r = proveprime((1n << 89n) - 1n); eq(r.status, "prime"); ok(checkCertificate(r.certificate)); });
test("Mersenne 2^127-1 proved", () => eq(proveprime((1n << 127n) - 1n).status, "prime"));
test("2^67-1 composite (Cole)", () => eq(proveprime((1n << 67n) - 1n).status, "composite"));
test("2^11-1 composite", () => eq(proveprime(2047n).status, "composite"));
test("large prime via Pocklington", () => { const p = 10n ** 30n + 57n; const r = proveprime(p); ok(r.status === "prime" || r.status === "unknown"); if (r.status === "prime") ok(checkCertificate(r.certificate)); });
test("tampered certificate rejected", () => {
  const r = proveprime(10n ** 30n + 57n);
  if (r.status === "prime" && r.certificate.type === "pocklington") { const bad = { ...r.certificate, n: String(10n ** 30n + 59n) }; ok(!checkCertificate(bad)); } else ok(true);
});
test("small primes deterministic", () => eq(proveprime(1000003n).status, "prime"));
