// Quelvra local storage: IndexedDB database "quelvra". Nothing leaves the device.
//
// Stores: history, saved, prefs, corrections, benchmarks, userFunctions, bugCases.
// Every call is wrapped: if IndexedDB is unavailable (private mode, blocked storage) the app
// keeps working with an in-memory fallback for the current session.

const DB_NAME = "quelvra";
const DB_VERSION = 1;
export const STORES = ["history", "saved", "prefs", "corrections", "benchmarks", "userFunctions", "bugCases"];
const KEYS = { prefs: "key" }; // others use an autoIncrement "id"

let dbPromise = null;
let persistent = false;
const memory = new Map(STORES.map((s) => [s, new Map()]));
let memSeq = 1;

function reqP(req) {
  return new Promise((res, rej) => { req.onsuccess = () => res(req.result); req.onerror = () => rej(req.error); });
}

function open() {
  if (dbPromise) return dbPromise;
  dbPromise = new Promise((resolve) => {
    try {
      if (typeof indexedDB === "undefined") { resolve(null); return; }
      const req = indexedDB.open(DB_NAME, DB_VERSION);
      req.onupgradeneeded = () => {
        const db = req.result;
        for (const s of STORES) {
          if (db.objectStoreNames.contains(s)) continue;
          const os = KEYS[s] ? db.createObjectStore(s, { keyPath: KEYS[s] }) : db.createObjectStore(s, { keyPath: "id", autoIncrement: true });
          if (s === "history") { os.createIndex("ts", "ts"); os.createIndex("pinned", "pinned"); }
        }
      };
      req.onsuccess = () => { persistent = true; resolve(req.result); };
      req.onerror = () => resolve(null);
      req.onblocked = () => resolve(null);
    } catch (_) {
      resolve(null);
    }
  });
  return dbPromise;
}

export const isPersistent = async () => { await open(); return persistent; };

async function tx(store, mode, fn) {
  const db = await open();
  if (!db) return null;
  try {
    const t = db.transaction(store, mode);
    const os = t.objectStore(store);
    const out = await fn(os);
    await new Promise((res, rej) => { t.oncomplete = res; t.onerror = () => rej(t.error); t.onabort = () => rej(t.error); });
    return { value: out };
  } catch (_) {
    return null;
  }
}

export async function put(store, value) {
  const v = { ...value };
  const r = await tx(store, "readwrite", (os) => reqP(os.put(v)));
  if (r) { if (!KEYS[store]) v.id = r.value; return v; }
  const key = KEYS[store] ? v[KEYS[store]] : (v.id ??= memSeq++);
  memory.get(store).set(key, v);
  return v;
}

export async function get(store, key) {
  const r = await tx(store, "readonly", (os) => reqP(os.get(key)));
  if (r) return r.value ?? null;
  return memory.get(store).get(key) ?? null;
}

export async function getAll(store) {
  const r = await tx(store, "readonly", (os) => reqP(os.getAll()));
  if (r) return r.value || [];
  return [...memory.get(store).values()];
}

export async function del(store, key) {
  const r = await tx(store, "readwrite", (os) => reqP(os.delete(key)));
  if (!r) memory.get(store).delete(key);
  return true;
}

export async function clear(store) {
  const r = await tx(store, "readwrite", (os) => reqP(os.clear()));
  if (!r) memory.get(store).clear();
  return true;
}

// ---------- convenience ----------
export async function getPref(key, fallback) {
  try {
    const rec = await get("prefs", key);
    return rec ? rec.value : fallback;
  } catch (_) {
    return fallback;
  }
}
export const setPref = (key, value) => put("prefs", { key, value }).catch(() => null);

const HISTORY_LIMIT = 500;
export async function addHistory(entry) {
  const rec = await put("history", { pinned: false, ts: Date.now(), ...entry });
  // keep the store bounded: drop the oldest unpinned entries
  try {
    const all = await getAll("history");
    if (all.length > HISTORY_LIMIT) {
      const drop = all.filter((h) => !h.pinned).sort((a, b) => a.ts - b.ts).slice(0, all.length - HISTORY_LIMIT);
      for (const h of drop) await del("history", h.id);
    }
  } catch (_) {}
  return rec;
}
export async function listHistory() {
  const all = await getAll("history");
  return all.sort((a, b) => (b.pinned - a.pinned) || b.ts - a.ts);
}
export async function exportAll() {
  const out = { format: "quelvra-export", version: 1, exported: new Date().toISOString(), stores: {} };
  for (const s of STORES) out.stores[s] = await getAll(s);
  return out;
}
