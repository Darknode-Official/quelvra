// Quelvra research lab: resource budget shared by every bounded computation.
//
// Every loop in engine/research calls budget.tick(k). The budget throws an Error with
// code "TIMEOUT" (wall clock) or "BUDGET" (operation count) instead of hanging, and reports
// progress through an optional callback so a Web Worker can post it to the UI.

const now = () => (typeof performance !== "undefined" ? performance.now() : Date.now());
export { now };

export function budgetError(code, message) {
  const e = new Error(message);
  e.code = code;
  return e;
}

export class Budget {
  constructor(opts = {}) {
    this.t0 = now();
    this.timeMs = opts.timeMs ?? 20000;
    this.deadline = opts.deadline ?? this.t0 + this.timeMs;
    this.maxOps = opts.ops ?? Infinity;
    this.ops = 0;
    this.onProgress = typeof opts.onProgress === "function" ? opts.onProgress : null;
    this.what = opts.what || "computation";
    this._nextCheck = 0;
    this._lastProgress = -1;
  }
  tick(n = 1) {
    this.ops += n;
    if (this.ops > this.maxOps) throw budgetError("BUDGET", `Operation budget exhausted during ${this.what}. Use a smaller bound or raise the ops option.`);
    if (this.ops >= this._nextCheck) {
      this._nextCheck = this.ops + 50000;
      if (now() > this.deadline) throw budgetError("TIMEOUT", `Time limit reached during ${this.what}. Use a smaller bound or raise the timeMs option.`);
    }
  }
  check() { if (now() > this.deadline) throw budgetError("TIMEOUT", `Time limit reached during ${this.what}.`); }
  progress(fraction, info) {
    if (!this.onProgress) return;
    const f = Math.max(0, Math.min(1, fraction));
    if (f - this._lastProgress < 0.01 && f < 1) return;
    this._lastProgress = f;
    try { this.onProgress(f, info || this.what); } catch (_) { /* never let the UI break the engine */ }
  }
  elapsed() { return now() - this.t0; }
}

export const asBudget = (opts = {}, what) => (opts instanceof Budget ? opts : opts.budget instanceof Budget ? opts.budget : new Budget({ ...opts, what }));

// Integer argument helpers (accept number, bigint, numeric string such as "10^6", "1e6", "1,000,000").
export function toBigIntArg(x, name = "argument") {
  if (typeof x === "bigint") return x;
  if (typeof x === "number") {
    if (!Number.isFinite(x) || !Number.isInteger(x)) throw budgetError("UNSUPPORTED", `${name} must be an integer`);
    return BigInt(x);
  }
  if (typeof x === "string") {
    const v = parseIntText(x);
    if (v === null) throw budgetError("UNSUPPORTED", `${name} must be an integer, got "${x}"`);
    return v;
  }
  if (x && typeof x === "object" && x.n !== undefined && x.d === 1n) return x.n;
  throw budgetError("UNSUPPORTED", `${name} must be an integer`);
}
// "10^6", "1e6", "1,000,000", "2^20", "5 million", "3*10^5" -> BigInt, or null.
export function parseIntText(s) {
  let t = String(s).trim().toLowerCase().replace(/[,_](?=\d{3})/g, "").replace(/\s+/g, " ");
  const scale = { thousand: 1000n, million: 1000000n, billion: 1000000000n, trillion: 1000000000000n };
  let m = t.match(/^(\d+) ?(thousand|million|billion|trillion)$/);
  if (m) return BigInt(m[1]) * scale[m[2]];
  m = t.match(/^(\d+)$/);
  if (m) return BigInt(m[1]);
  m = t.match(/^(\d+)(?:\.(\d+))?e\+?(\d+)$/);
  if (m) {
    const frac = m[2] || "", e = Number(m[3]);
    if (frac.length > e) return null;
    return BigInt(m[1] + frac) * 10n ** BigInt(e - frac.length);
  }
  return intExpr(t);
}
// Tiny integer expression evaluator (no eval): + - * x ^ ** and parentheses on BigInt, e-notation literals.
function intExpr(src) {
  const toks = String(src).replace(/\*\*/g, "^").match(/\d+(?:\.\d+)?e\+?\d+|\d+|[-+*x^()]|\S/g);
  if (!toks) return null;
  let i = 0;
  const peek = () => toks[i];
  const lit = (tk) => { const m = tk.match(/^(\d+)(?:\.(\d+))?e\+?(\d+)$/); if (!m) return /^\d+$/.test(tk) ? BigInt(tk) : null; const f = m[2] || "", e = Number(m[3]); return f.length > e ? null : BigInt(m[1] + f) * 10n ** BigInt(e - f.length); };
  const atom = () => {
    const tk = toks[i++];
    if (tk === "(") { const v = sum(); if (toks[i++] !== ")") throw 0; return v; }
    if (tk === "-") return -atom();
    const v = tk === undefined ? null : lit(tk); if (v === null) throw 0; return v;
  };
  const power = () => { const b = atom(); if (peek() === "^") { i++; const e = power(); if (e < 0n || e > 4096n) throw 0; return b ** e; } return b; };
  const prod = () => { let v = power(); while (peek() === "*" || peek() === "x") { i++; v *= power(); } return v; };
  const sum = () => { let v = prod(); while (peek() === "+" || peek() === "-") { const op = toks[i++]; const w = prod(); v = op === "+" ? v + w : v - w; } return v; };
  try { const v = sum(); return i === toks.length ? v : null; } catch (_) { return null; }
}
export const fmtInt = (n) => { const s = String(n); return s.length <= 4 ? s : s.replace(/\B(?=(\d{3})+(?!\d))/g, ","); };
