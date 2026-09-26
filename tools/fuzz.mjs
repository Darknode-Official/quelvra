// Quelvra differential + metamorphic fuzzer.
//
//   node tools/fuzz.mjs [--seed 1] [--scale 1] [--cat eq-poly,ineq] [--jobs 8] [--no-oracle] [--out file.json] [-v]
//
// Generates seeded random problems in every category (tools/fuzz-lib.mjs), solves each one
// with Quelvra, and judges every VERIFIED answer three ways:
//   1. oracle-free checks in JS: independent substitution into the generator's own expression,
//      parse/print round trips, roots known by construction;
//   2. metamorphic groups: the same problem written differently (sides swapped, scaled, factored,
//      variable renamed, other phrasing) must give the same verified answer set;
//   3. the sympy/mpmath oracle (tools/fuzz-oracle.py through python3), a TEST-ONLY dependency.
// Also records refusals, crashes and cases slower than 2 s.
import { fork, spawnSync } from "node:child_process";
import { writeFileSync, readFileSync, mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, dirname } from "node:path";
import { fileURLToPath } from "node:url";

const HERE = dirname(fileURLToPath(import.meta.url));
const argv = process.argv.slice(2);
const opt = (name, def) => { const i = argv.indexOf("--" + name); return i >= 0 ? argv[i + 1] : def; };
const flag = (name) => argv.includes("--" + name) || argv.includes("-" + name);

if (flag("worker")) await worker();
else await main();

async function worker() {
  const L = await import("./fuzz-lib.mjs");
  process.on("message", (job) => {
    const out = [];
    const cases = L.generate(job.cat, job.count, job.seed);
    for (let i = 0; i < cases.length; i++) {
      const c = cases[i];
      const id = `${c.group}/${c.variant}`;
      if (c.cat === "parse") {
        const t = performance.now();
        const probs = L.checkParse(c);
        out.push({ id, cat: c.cat, group: c.group, variant: c.variant, input: c.input, claim: { verified: !probs.some((p) => p.type === "refusal"), ms: performance.now() - t, answers: [] }, js: probs, key: null, task: null });
        continue;
      }
      const run = L.runCase(c.input, job.timeLimit);
      const r = run.tree;
      delete run.tree;
      const js = [];
      try {
        if (c.gl) js.push(...L.checkSubstitution(c, r));
        if (c.truth) js.push(...L.checkEqTruth(c, r));
      } catch (e) { js.push({ type: "harness", detail: String(e.message) }); }
      let key = null;
      try { key = L.answerKey(r); } catch (_) { key = null; }
      out.push({ id, cat: c.cat, group: c.group, variant: c.variant, input: c.input, claim: run, js, key, task: c.task });
    }
    process.send(out);
  });
}

async function main() {
  const L = await import("./fuzz-lib.mjs");
  const seed = +opt("seed", 1);
  const scale = +opt("scale", 1);
  const jobs = +opt("jobs", 8);
  const cats = opt("cat", Object.keys(L.CATEGORY_WEIGHTS).join(",")).split(",");
  const useOracle = !flag("no-oracle");
  const verbose = flag("v");
  const outFile = opt("out", null);
  const timeLimit = +opt("time", 8000);

  // shards: each (category, shard) pair is a deterministic job
  const shardSize = 150;
  const queue = [];
  for (const cat of cats) {
    const total = Math.max(1, Math.round(L.CATEGORY_WEIGHTS[cat] * scale));
    for (let s = 0; s * shardSize < total; s++) queue.push({ cat, count: Math.min(shardSize, total - s * shardSize), seed: seed * 100003 + hash(cat) * 7919 + s, timeLimit });
  }
  const t0 = Date.now();
  const records = [];
  await new Promise((resolve) => {
    let active = 0, done = 0;
    const next = () => {
      if (!queue.length) { if (!active) resolve(); return; }
      const job = queue.shift();
      active++;
      const child = fork(fileURLToPath(import.meta.url), ["--worker"], { stdio: ["ignore", "inherit", "inherit", "ipc"] });
      child.on("message", (res) => { records.push(...res); child.kill(); });
      child.on("exit", () => { active--; done++; if (process.stderr.isTTY) process.stderr.write(`\r  engine shards done ${done}   `); next(); });
      child.send(job);
    };
    for (let i = 0; i < jobs; i++) next();
  });
  if (process.stderr.isTTY) process.stderr.write("\n");
  const engineSec = (Date.now() - t0) / 1000;

  // oracle
  const verdicts = new Map();
  if (useOracle) {
    const todo = records.filter((r) => r.task && r.claim.verified);
    const dir = mkdtempSync(join(tmpdir(), "qfuzz-"));
    const chunk = 3000;
    for (let i = 0; i < todo.length; i += chunk) {
      const part = todo.slice(i, i + chunk).map((r) => ({ id: r.id, task: r.task, claim: r.claim }));
      const f = join(dir, "in.json");
      writeFileSync(f, JSON.stringify(part));
      const p = spawnSync("python3", [join(HERE, "fuzz-oracle.py")], { input: readFileSync(f), maxBuffer: 1 << 30, env: { ...process.env, ORACLE_JOBS: String(opt("ojobs", 14)) } });
      if (p.status !== 0) { console.error(String(p.stderr).slice(-3000)); process.exit(2); }
      for (const v of JSON.parse(String(p.stdout))) verdicts.set(v.id, v);
      if (process.stderr.isTTY) process.stderr.write(`\r  oracle ${Math.min(i + chunk, todo.length)}/${todo.length}   `);
    }
    rmSync(dir, { recursive: true, force: true });
    if (process.stderr.isTTY) process.stderr.write("\n");
  }

  // aggregate
  const stats = new Map();
  const issues = [];
  const S = (cat) => { if (!stats.has(cat)) stats.set(cat, { total: 0, verified: 0, refused: 0, crash: 0, slow: 0, wrong: 0, wrongJS: 0, unknown: 0, groupMismatch: 0, groupRefusal: 0 }); return stats.get(cat); };
  for (const r of records) {
    const s = S(r.cat);
    s.total++;
    if (r.claim.crash) { s.crash++; issues.push({ type: "crash", cat: r.cat, input: r.input, detail: r.claim.crash }); }
    if (r.claim.ms > 2000) { s.slow++; issues.push({ type: "slow", cat: r.cat, input: r.input, detail: `${Math.round(r.claim.ms)} ms` }); }
    if (r.claim.verified) s.verified++; else s.refused++;
    const wjs = r.js.filter((p) => p.type === "wrong");
    if (wjs.length) { s.wrongJS++; issues.push({ type: "wrong-js", cat: r.cat, input: r.input, answer: r.claim.text, detail: wjs.map((p) => p.detail).join("; ") }); }
    const v = verdicts.get(r.id);
    if (v && v.verdict === "wrong") { s.wrong++; issues.push({ type: "wrong-oracle", cat: r.cat, input: r.input, answer: r.claim.text, detail: v.detail }); }
    if (v && v.verdict === "unknown") { s.unknown++; if (verbose) issues.push({ type: "oracle-unknown", cat: r.cat, input: r.input, answer: r.claim.text, detail: v.detail }); }
  }
  const groups = new Map();
  for (const r of records) { if (r.cat === "parse") continue; if (!groups.has(r.group)) groups.set(r.group, []); groups.get(r.group).push(r); }
  for (const [g, rs] of groups) {
    const ver = rs.filter((r) => r.claim.verified && r.key != null);
    const keys = new Set(ver.map((r) => r.key));
    if (keys.size > 1) { S(rs[0].cat).groupMismatch++; issues.push({ type: "group-mismatch", cat: rs[0].cat, group: g, detail: ver.map((r) => `${r.variant}: ${r.input}  ->  ${r.claim.text}`).join("\n      ") }); }
    if (ver.length && ver.length < rs.length) { S(rs[0].cat).groupRefusal++; issues.push({ type: "group-refusal", cat: rs[0].cat, group: g, detail: rs.map((r) => `${r.variant}: ${r.input}  ->  ${r.claim.verified ? r.claim.text : "REFUSED " + (r.claim.error || (r.claim.answers[0] && r.claim.answers[0].label) || "")}`).join("\n      ") }); }
  }

  const tot = { total: 0, verified: 0, refused: 0, crash: 0, slow: 0, wrong: 0, wrongJS: 0, unknown: 0, groupMismatch: 0, groupRefusal: 0 };
  console.log(`${"category".padEnd(14)} ${"cases".padStart(6)} ${"verif".padStart(6)} ${"refus".padStart(6)} ${"WRONG".padStart(6)} ${"wrgJS".padStart(6)} ${"grpMM".padStart(6)} ${"grpRf".padStart(6)} ${"crash".padStart(6)} ${"slow".padStart(5)} ${"unkn".padStart(5)}`);
  for (const [cat, s] of stats) {
    console.log(`${cat.padEnd(14)} ${String(s.total).padStart(6)} ${String(s.verified).padStart(6)} ${String(s.refused).padStart(6)} ${String(s.wrong).padStart(6)} ${String(s.wrongJS).padStart(6)} ${String(s.groupMismatch).padStart(6)} ${String(s.groupRefusal).padStart(6)} ${String(s.crash).padStart(6)} ${String(s.slow).padStart(5)} ${String(s.unknown).padStart(5)}`);
    for (const k in tot) tot[k] += s[k];
  }
  console.log(`${"TOTAL".padEnd(14)} ${String(tot.total).padStart(6)} ${String(tot.verified).padStart(6)} ${String(tot.refused).padStart(6)} ${String(tot.wrong).padStart(6)} ${String(tot.wrongJS).padStart(6)} ${String(tot.groupMismatch).padStart(6)} ${String(tot.groupRefusal).padStart(6)} ${String(tot.crash).padStart(6)} ${String(tot.slow).padStart(5)} ${String(tot.unknown).padStart(5)}`);
  console.log(`engine ${engineSec.toFixed(1)} s, total ${((Date.now() - t0) / 1000).toFixed(1)} s`);
  const show = issues.filter((i) => verbose || i.type !== "group-refusal");
  for (const i of show.slice(0, +opt("show", 60))) console.log(`\n[${i.type}] (${i.cat}) ${i.input || i.group}\n      ${i.answer ? "answer: " + i.answer + "\n      " : ""}${i.detail}`);
  if (outFile) writeFileSync(outFile, JSON.stringify({ stats: Object.fromEntries(stats), issues, records: flag("records") ? records : undefined }, null, 1));
  process.exit(tot.wrong + tot.wrongJS + tot.groupMismatch + tot.crash ? 1 : 0);
}

function hash(s) { let h = 7; for (const ch of s) h = (h * 31 + ch.charCodeAt(0)) >>> 0; return h % 10007; }
