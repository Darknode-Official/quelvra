// Quelvra test runner: node test/quelvra/run.js [filter]
import { readdirSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { TESTS, setFile } from "./harness.js";

const dir = dirname(fileURLToPath(import.meta.url));
const filter = process.argv[2] || "";
const files = readdirSync(dir).filter((f) => f.endsWith(".test.js") && f.includes(filter)).sort();

for (const f of files) {
  setFile(f);
  await import(pathToFileURL(join(dir, f)).href);
}

let pass = 0, fail = 0;
const byFile = new Map();
const t0 = performance.now();
for (const t of TESTS) {
  const s = performance.now();
  try {
    await t.fn();
    pass++;
    byFile.set(t.file, (byFile.get(t.file) || { p: 0, f: 0 }));
    byFile.get(t.file).p++;
  } catch (e) {
    fail++;
    byFile.set(t.file, (byFile.get(t.file) || { p: 0, f: 0 }));
    byFile.get(t.file).f++;
    console.log(`FAIL ${t.file} :: ${t.name}\n     ${e && e.message}`);
    if (process.env.QV_STACK) console.log(e.stack);
  }
  const ms = performance.now() - s;
  if (ms > 2000) console.log(`SLOW ${t.file} :: ${t.name} (${ms.toFixed(0)} ms)`);
}
for (const [f, r] of byFile) console.log(`${r.f ? "x" : "ok"} ${f.padEnd(28)} ${r.p} passed${r.f ? `, ${r.f} failed` : ""}`);
console.log(`\n${pass} passed, ${fail} failed, ${TESTS.length} total in ${((performance.now() - t0) / 1000).toFixed(2)} s`);
process.exit(fail ? 1 : 0);
