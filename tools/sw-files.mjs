// Regenerates the FILES precache list in public/sw.js from the files on disk and bumps VERSION.
// Run before deploying: node tools/sw-files.mjs
import { readFileSync, writeFileSync, readdirSync, statSync } from "node:fs";
import { join, relative } from "node:path";
const root = new URL("../public/", import.meta.url).pathname;
const walk = (d) => readdirSync(d).flatMap((f) => { const p = join(d, f); return statSync(p).isDirectory() ? walk(p) : [p]; });
const files = walk(root).map((p) => relative(root, p)).filter((f) => f !== "sw.js" && !f.endsWith(".md") && !f.includes("test")).sort();
const swPath = join(root, "sw.js");
let sw = readFileSync(swPath, "utf8");
const list = ["", ...files].map((f) => `  ${JSON.stringify(f)},`).join("\n");
sw = sw.replace(/const FILES = \[[\s\S]*?\]\.map/, `const FILES = [\n${list}\n].map`);
sw = sw.replace(/const VERSION = "quelvra-[^"]*";/, `const VERSION = "quelvra-${Date.now().toString(36)}";`);
writeFileSync(swPath, sw);
console.log(`sw.js: ${files.length + 1} files precached`);
