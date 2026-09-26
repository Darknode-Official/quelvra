// Quelvra page-side bridge to the compute worker.
//
//   solve(input, options, { onProgress, timeoutMs })     -> Job (Promise + cancel())
//   checkWork(lines, options, { onProgress, timeoutMs }) -> Job
//   numeric(input, options, ...)                         -> Job
//   preview(input)                                       -> Job (runs on a separate worker lane)
//
// Every job resolves with a deserialised result (trees rebuilt as record.node) or rejects with
// { code, message, pos, hint }. cancel() terminates the worker and a fresh one is spawned for
// the next job, so no input can freeze the page. Codes added here: CANCELLED, TIMEOUT, WORKER.

import { deserializeResult } from "./bridge-shared.js";

const WORKER_URL = new URL("./worker.js", import.meta.url);

class Lane {
  constructor(name, defaultTimeout) {
    this.name = name;
    this.defaultTimeout = defaultTimeout;
    this.worker = null;
    this.pending = new Map();
    this.seq = 0;
  }
  spawn() {
    if (this.worker) return this.worker;
    const w = new Worker(WORKER_URL, { type: "module", name: "quelvra-" + this.name });
    w.onmessage = (ev) => this.onMessage(ev.data || {});
    w.onerror = (ev) => {
      ev.preventDefault?.();
      this.failAll({ code: "WORKER", message: "The compute worker failed: " + (ev.message || "unknown error"), pos: null, hint: "" });
      this.kill();
    };
    w.onmessageerror = () => this.failAll({ code: "WORKER", message: "A message from the worker could not be read", pos: null, hint: "" });
    this.worker = w;
    return w;
  }
  kill() {
    if (this.worker) { try { this.worker.terminate(); } catch (_) {} }
    this.worker = null;
  }
  failAll(error) {
    for (const [, p] of this.pending) { clearTimeout(p.timer); p.reject(error); }
    this.pending.clear();
  }
  onMessage(msg) {
    const p = this.pending.get(msg.id);
    if (!p) return;
    if (msg.type === "progress") { try { p.onProgress?.(msg.stage); } catch (_) {} return; }
    this.pending.delete(msg.id);
    clearTimeout(p.timer);
    if (msg.type === "result") {
      let out;
      try { out = deserializeResult(msg.result); } catch (e) { p.reject({ code: "WORKER", message: "Could not read result: " + e.message, pos: null, hint: "" }); return; }
      p.resolve(out);
    } else if (msg.type === "error") p.reject(msg.error || { code: "ENGINE", message: "Unknown error", pos: null, hint: "" });
  }
  // Abort one job. The worker is single-threaded and busy, so terminating is the only real abort;
  // other jobs on this lane are rejected too (the app runs one at a time per lane).
  abort(id, error) {
    if (!this.pending.has(id)) return false;
    this.kill();
    this.failAll(error);
    return true;
  }
  run(type, input, options, { onProgress, timeoutMs } = {}) {
    const id = ++this.seq;
    let resolve, reject;
    const promise = new Promise((res, rej) => { resolve = res; reject = rej; });
    const limit = timeoutMs ?? this.defaultTimeout;
    const entry = { resolve, reject, onProgress, timer: 0 };
    this.pending.set(id, entry);
    if (limit > 0) {
      entry.timer = setTimeout(() => this.abort(id, { code: "TIMEOUT", message: `Stopped after ${Math.round(limit / 1000)} s without an answer`, pos: null, hint: "Try a smaller problem, or ask for a numeric answer" }), limit);
    }
    try {
      this.spawn().postMessage({ id, type, input, options: options || {} });
    } catch (e) {
      this.pending.delete(id);
      clearTimeout(entry.timer);
      reject({ code: "WORKER", message: "Could not start the compute worker: " + (e.message || e), pos: null, hint: "" });
    }
    const job = promise;
    job.id = id;
    job.cancel = () => this.abort(id, { code: "CANCELLED", message: "Cancelled", pos: null, hint: "" });
    return job;
  }
}

const solveLane = new Lane("solve", 60000);
const previewLane = new Lane("preview", 4000);

export const solve = (input, options, extra) => solveLane.run("solve", input, options, extra);
export const checkWork = (lines, options, extra) => solveLane.run("check-work", lines, options, extra);
export const numeric = (input, options, extra) => solveLane.run("numeric", input, options, extra);
export const preview = (input, extra) => previewLane.run("preview", input, {}, extra);
export const cancelAll = () => { solveLane.abort([...solveLane.pending.keys()][0], { code: "CANCELLED", message: "Cancelled", pos: null, hint: "" }); };
export const isBusy = () => solveLane.pending.size > 0;
