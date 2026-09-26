// Quelvra ink: handwriting and photo input for the Solve tab.
//
// Recognition runs on this device through engine/vision (loaded lazily on first use); nothing is
// uploaded. Vision only translates ink into text: the user reviews every symbol, low-confidence
// ones are highlighted with their alternatives, and "Use this" only fills the problem box. It
// never solves.
//
//   initInk({ h, icon, toast, syntaxErrorView, store, textarea, use(text) })

const PHOTO_MAX = 1600;           // longest side of the decoded photo, in pixels
const PREF_TEMPLATES = "visionTemplates";

export function initInk(deps) {
  const { h, icon, toast, syntaxErrorView, store, textarea, use } = deps;
  const $ = (id) => document.getElementById(id);
  const panel = $("ink"), btnDraw = $("btn-draw"), btnPhoto = $("btn-photo"), fileInput = $("ink-file");
  if (!panel || !btnDraw || !btnPhoto || !fileInput) return null;

  // ---------------- vision engine (lazy) ----------------
  let visionP = null, photoReady = null, parse = null;
  function vision() {
    visionP ||= Promise.all([import("./engine/vision/index.js"), import("./engine/parse.js")]).then(async ([V, P]) => {
      parse = P.parse;
      try {
        const saved = await store.getPref(PREF_TEMPLATES, null);
        if (saved) V.importTemplates(saved, { replace: true });
      } catch (_) { /* a damaged template record must not stop recognition */ }
      return V;
    });
    return visionP;
  }
  // Font templates rendered from the fonts installed on this device, built once before the first photo.
  function photoTemplates(V) {
    photoReady ||= (async () => {
      try {
        const render = V.browserFontRenderer();
        if (render) V.setPhotoTemplates(V.buildFontTemplates(render));
      } catch (_) { /* the built-in pen templates still work */ }
    })();
    return photoReady;
  }
  const nextFrame = () => new Promise((r) => requestAnimationFrame(() => setTimeout(r, 0)));
  const css = (name, fallback) => (getComputedStyle(document.documentElement).getPropertyValue(name).trim() || fallback);

  // ---------------- state ----------------
  const st = {
    mode: null,          // "draw" | "photo" | null
    strokes: [],         // [[{x, y, t}]] in CSS pixels, y down: the format strokes.js expects
    drawing: null,       // stroke in progress
    pointerId: null,
    result: null,        // raw vision result
    tokens: [],          // toEditable(result), texts updated by corrections
    active: -1,          // token index whose alternatives are shown
    manual: false,       // the text field was edited by hand, chips no longer describe it
    photo: null,         // { canvas, skewed }
    busy: false,
    lastFix: null,       // { char, strokeIds } of the latest correction, offered for teaching
  };

  // ---------------- DOM ----------------
  const title = h("h2", { id: "ink-h" }, "Handwriting");
  const closeBtn = h("button", { type: "button", class: "btn ghost icon-only", "aria-label": "Close", onclick: () => close() }, icon("x"));

  const canvas = h("canvas", { class: "ink-canvas", tabindex: "0", role: "img", "aria-label": "Drawing area. Write one expression with a mouse, pen or finger, then press Recognize." });
  const hint = h("div", { class: "ink-hint", "aria-hidden": "true" }, "Write here");
  const pad = h("div", { class: "ink-pad" }, canvas, hint);
  const btnUndo = h("button", { type: "button", class: "btn small", onclick: () => undo() }, icon("undo"), "Undo");
  const btnClear = h("button", { type: "button", class: "btn small", onclick: () => clearInk() }, icon("trash"), "Clear");
  const btnRecognize = h("button", { type: "button", class: "btn small primary", onclick: () => recognizeDrawing() }, "Recognize");
  const taught = h("span", { class: "ink-taught tiny muted" });
  const drawTools = h("div", { class: "ink-tools" }, btnUndo, btnClear, h("span", { class: "ink-spacer" }), btnRecognize);
  const drawBox = h("div", { class: "ink-draw" }, pad, drawTools);

  const photoCanvas = h("canvas", { class: "ink-photo-canvas", role: "img", "aria-label": "The photo being read" });
  const btnAnother = h("button", { type: "button", class: "btn small", onclick: () => fileInput.click() }, icon("image"), "Choose another photo");
  const photoBox = h("div", { class: "ink-photo" }, h("div", { class: "ink-photo-wrap" }, photoCanvas), h("div", { class: "ink-tools" }, btnAnother, h("span", { class: "tiny muted" }, "The photo stays on this device.")));

  const status = h("p", { class: "ink-status small-t", role: "status", "aria-live": "polite" });

  const legend = h("span", { class: "tiny muted ink-legend" }, "Highlighted symbols are uncertain: select one to see what else it could be.");
  const chips = h("div", { class: "ink-chips", role: "group", "aria-label": "Recognized symbols" });
  const alts = h("div", { class: "ink-alts", hidden: true });
  const textField = h("input", { type: "text", class: "field ink-text", id: "ink-text", spellcheck: "false", autocomplete: "off", autocapitalize: "off" });
  const parseBox = h("div", { class: "ink-parse", "aria-live": "polite" });
  const teach = h("div", { class: "ink-teach", hidden: true });
  const btnUse = h("button", { type: "button", class: "btn primary", onclick: () => useText() }, icon("check"), "Use this");
  const btnCancel = h("button", { type: "button", class: "btn", onclick: () => close() }, "Cancel");
  const review = h("div", { class: "ink-review", hidden: true },
    h("div", { class: "ink-sub" }, "Recognized", legend),
    chips, alts,
    h("label", { class: "ink-sub", for: "ink-text" }, "Text"),
    textField, parseBox, teach);
  const footer = h("div", { class: "ink-foot" }, taught, h("span", { class: "ink-spacer" }), btnCancel, btnUse);

  panel.replaceChildren(h("div", { class: "ink-head" }, title, closeBtn), drawBox, photoBox, status, review, footer);
  panel.setAttribute("tabindex", "-1");

  // ---------------- open / close ----------------
  function open(mode) {
    st.mode = mode;
    panel.hidden = false;
    panel.dataset.mode = mode;
    title.textContent = mode === "draw" ? "Handwriting" : "Photo";
    drawBox.hidden = mode !== "draw";
    photoBox.hidden = mode !== "photo";
    btnDraw.setAttribute("aria-expanded", String(mode === "draw"));
    btnPhoto.setAttribute("aria-expanded", String(mode === "photo"));
    resetReview();
    setStatus("");
    if (mode === "draw") {
      sizeCanvas();
      redraw();
      canvas.focus({ preventScroll: true });
      panel.scrollIntoView({ block: "nearest", behavior: "auto" });
      setStatus(st.strokes.length ? "" : "Write the expression, then press Recognize.");
      vision().then(updateTaught).catch(() => {}); // warm up while the user writes
    } else {
      taught.replaceChildren();
      panel.focus({ preventScroll: true });
    }
    updateButtons();
  }
  function close() {
    if (panel.hidden) return;
    panel.hidden = true;
    st.mode = null;
    closeAlts(false);
    btnDraw.setAttribute("aria-expanded", "false");
    btnPhoto.setAttribute("aria-expanded", "false");
    textarea.focus();
  }
  function resetReview() {
    st.result = null; st.tokens = []; st.active = -1; st.manual = false; st.lastFix = null;
    review.hidden = true;
    alts.hidden = true;
    teach.hidden = true;
    chips.replaceChildren();
    parseBox.replaceChildren();
    textField.value = "";
    updateButtons();
  }
  function setStatus(msg, kind = "") {
    status.textContent = msg;
    status.className = "ink-status small-t" + (kind ? " " + kind : "");
    status.hidden = !msg;
  }
  function updateButtons() {
    const empty = !st.strokes.length;
    btnUndo.disabled = empty || st.busy;
    btnClear.disabled = empty || st.busy;
    btnRecognize.disabled = empty || st.busy;
    btnUse.disabled = review.hidden || !textField.value.trim();
    hint.hidden = !empty;
  }
  async function updateTaught() {
    let n = 0;
    try { const V = await vision(); n = (JSON.parse(V.exportTemplates()).strokes || []).length; } catch (_) { n = 0; }
    taught.replaceChildren();
    if (st.mode === "draw" && n) {
      taught.append(`${n} handwriting sample${n > 1 ? "s" : ""} taught. `,
        h("button", { type: "button", class: "linkish", onclick: forgetSamples }, "Forget them"));
    }
  }
  async function forgetSamples() {
    try {
      const V = await vision();
      V.clearTemplates();
      await store.setPref(PREF_TEMPLATES, null);
      toast("Handwriting samples removed");
    } catch (_) { toast("Could not remove the samples"); }
    updateTaught();
  }

  // ---------------- canvas ----------------
  let cssW = 0, cssH = 0, rect = null;
  function sizeCanvas() {
    const r = pad.getBoundingClientRect();
    const dpr = Math.max(1, Math.min(window.devicePixelRatio || 1, 3));
    cssW = Math.max(1, Math.round(r.width));
    cssH = Math.max(1, Math.round(r.height));
    const w = Math.round(cssW * dpr), hgt = Math.round(cssH * dpr);
    if (canvas.width !== w || canvas.height !== hgt) { canvas.width = w; canvas.height = hgt; }
    canvas.getContext("2d").setTransform(dpr, 0, 0, dpr, 0, 0);
  }
  function strokeColor(i) {
    const sym = st.result && !st.manual ? symbolOfStroke(i) : -1;
    if (sym >= 0 && st.active >= 0 && st.tokens[st.active] && st.tokens[st.active].symbol === sym) return css("--acc", "#0575a6");
    if (sym >= 0 && st.tokens.some((t) => t.symbol === sym && t.uncertain && !t.fixed)) return css("--warn", "#8a6314");
    return css("--txt", "#111826");
  }
  function symbolOfStroke(i) {
    const syms = (st.result && st.result.symbols) || [];
    for (let k = 0; k < syms.length; k++) if ((syms[k].strokeIds || []).includes(i)) return k;
    return -1;
  }
  function paintStroke(ctx, s, color) {
    ctx.strokeStyle = color; ctx.fillStyle = color;
    if (s.length === 1) { ctx.beginPath(); ctx.arc(s[0].x, s[0].y, 1.6, 0, Math.PI * 2); ctx.fill(); return; }
    ctx.beginPath();
    ctx.moveTo(s[0].x, s[0].y);
    for (let k = 1; k < s.length; k++) ctx.lineTo(s[k].x, s[k].y);
    ctx.stroke();
  }
  function redraw() {
    if (st.mode !== "draw") return;
    const ctx = canvas.getContext("2d");
    ctx.clearRect(0, 0, cssW, cssH);
    // writing guide: a faint baseline
    ctx.strokeStyle = css("--line", "#dbe2ee");
    ctx.lineWidth = 1;
    ctx.setLineDash([4, 6]);
    ctx.beginPath(); ctx.moveTo(12, cssH * 0.68); ctx.lineTo(cssW - 12, cssH * 0.68); ctx.stroke();
    ctx.setLineDash([]);
    ctx.lineWidth = 3; ctx.lineCap = "round"; ctx.lineJoin = "round";
    st.strokes.forEach((s, i) => paintStroke(ctx, s, strokeColor(i)));
    if (st.drawing) paintStroke(ctx, st.drawing, css("--txt", "#111826"));
  }
  function pointOf(e) { return { x: +(e.clientX - rect.left).toFixed(1), y: +(e.clientY - rect.top).toFixed(1), t: Math.round(e.timeStamp) }; }
  canvas.addEventListener("pointerdown", (e) => {
    if (st.busy || st.pointerId !== null || (e.pointerType === "mouse" && e.button !== 0)) return;
    e.preventDefault();
    st.pointerId = e.pointerId;
    try { canvas.setPointerCapture(e.pointerId); } catch (_) {}
    rect = canvas.getBoundingClientRect();
    st.drawing = [pointOf(e)];
    redraw();
  });
  canvas.addEventListener("pointermove", (e) => {
    if (e.pointerId !== st.pointerId || !st.drawing) return;
    e.preventDefault();
    const evs = typeof e.getCoalescedEvents === "function" ? e.getCoalescedEvents() : [];
    const s = st.drawing, from = s.length - 1;
    for (const ev of evs.length ? evs : [e]) s.push(pointOf(ev));
    const ctx = canvas.getContext("2d");
    ctx.strokeStyle = css("--txt", "#111826");
    ctx.lineWidth = 3; ctx.lineCap = "round"; ctx.lineJoin = "round";
    ctx.beginPath();
    ctx.moveTo(s[from].x, s[from].y);
    for (let k = from + 1; k < s.length; k++) ctx.lineTo(s[k].x, s[k].y);
    ctx.stroke();
  });
  function endStroke(e) {
    if (e.pointerId !== st.pointerId) return;
    st.pointerId = null;
    const s = st.drawing;
    st.drawing = null;
    if (s && s.length) {
      st.strokes.push(s);
      if (!review.hidden || st.result) { resetReview(); setStatus("Press Recognize to read the new ink."); }
      else setStatus("");
    }
    redraw();
    updateButtons();
  }
  canvas.addEventListener("pointerup", endStroke);
  canvas.addEventListener("pointercancel", endStroke);
  canvas.addEventListener("keydown", (e) => {
    if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === "z") { e.preventDefault(); undo(); }
    else if (e.key === "Enter" && st.strokes.length) { e.preventDefault(); recognizeDrawing(); }
  });
  if (typeof ResizeObserver === "function") {
    new ResizeObserver(() => { if (st.mode === "draw") { sizeCanvas(); redraw(); } }).observe(pad);
  }
  // ink colours come from the CSS tokens: repaint when the theme changes either way
  const repaintTheme = () => { redraw(); if (st.mode === "photo") paintPhoto(); };
  new MutationObserver(repaintTheme).observe(document.documentElement, { attributes: true, attributeFilter: ["data-theme"] });
  if (window.matchMedia) matchMedia("(prefers-color-scheme: dark)").addEventListener?.("change", repaintTheme);

  function undo() {
    if (!st.strokes.length) return;
    st.strokes.pop();
    resetReview();
    setStatus(st.strokes.length ? "Removed the last stroke." : "");
    redraw();
    updateButtons();
  }
  function clearInk() {
    st.strokes = [];
    resetReview();
    setStatus("Cleared.");
    redraw();
    updateButtons();
    canvas.focus({ preventScroll: true });
  }

  async function recognizeDrawing() {
    if (!st.strokes.length || st.busy) return;
    st.busy = true;
    updateButtons();
    setStatus("Reading your handwriting...");
    try {
      const V = await vision();
      await nextFrame();
      const result = V.recognizeStrokes(st.strokes.map((s) => s.map((p) => ({ ...p }))));
      showResult(V, result);
    } catch (err) {
      setStatus("Could not read the handwriting: " + ((err && err.message) || "unknown error"), "st-bad");
    } finally {
      st.busy = false;
      updateButtons();
    }
  }

  // ---------------- photo ----------------
  async function readPhoto(file) {
    if (!file || !/^image\//.test(file.type || "")) { toast("That file is not an image"); return; }
    open("photo");
    st.busy = true;
    st.photo = null;
    paintPhoto();
    setStatus("Decoding the photo...");
    try {
      let bmp;
      try { bmp = await createImageBitmap(file, { imageOrientation: "from-image" }); } catch (_) { bmp = await createImageBitmap(file); }
      const scale = Math.min(1, PHOTO_MAX / Math.max(bmp.width, bmp.height));
      const w = Math.max(1, Math.round(bmp.width * scale)), hgt = Math.max(1, Math.round(bmp.height * scale));
      const cv = document.createElement("canvas");
      cv.width = w; cv.height = hgt;
      const ctx = cv.getContext("2d", { willReadFrequently: true });
      ctx.fillStyle = "#fff"; // transparent screenshots read as white paper
      ctx.fillRect(0, 0, w, hgt);
      ctx.drawImage(bmp, 0, 0, w, hgt);
      if (bmp.close) bmp.close();
      const img = ctx.getImageData(0, 0, w, hgt);
      st.photo = { canvas: cv, skewed: false };
      paintPhoto();
      setStatus("Reading the photo...");
      const V = await vision();
      await nextFrame();
      await photoTemplates(V);
      await nextFrame();
      const result = V.recognizeImage(img);
      st.photo.skewed = !!(result.preprocess && (result.preprocess.width !== w || result.preprocess.height !== hgt));
      showResult(V, result);
      paintPhoto();
    } catch (err) {
      setStatus("Could not read this image: " + ((err && err.message) || "the browser cannot decode it"), "st-bad");
    } finally {
      st.busy = false;
      updateButtons();
    }
  }
  function paintPhoto() {
    const ph = st.photo;
    photoCanvas.hidden = !ph;
    if (!ph) return;
    const wrapW = Math.max(1, photoBox.getBoundingClientRect().width || 600);
    const maxH = window.innerWidth <= 640 ? 160 : 220;
    const s = Math.min(wrapW / ph.canvas.width, maxH / ph.canvas.height, 1.5);
    const w = Math.round(ph.canvas.width * s), hgt = Math.round(ph.canvas.height * s);
    const dpr = Math.max(1, Math.min(window.devicePixelRatio || 1, 3));
    photoCanvas.width = Math.round(w * dpr); photoCanvas.height = Math.round(hgt * dpr);
    photoCanvas.style.width = w + "px"; photoCanvas.style.height = hgt + "px";
    const ctx = photoCanvas.getContext("2d");
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.drawImage(ph.canvas, 0, 0, w, hgt);
    if (!st.result || st.manual || ph.skewed) return; // boxes are in deskewed coordinates then
    ctx.lineWidth = 2;
    st.result.symbols.forEach((sym, k) => {
      const tok = st.tokens.find((t) => t.symbol === k);
      const on = st.active >= 0 && st.tokens[st.active] && st.tokens[st.active].symbol === k;
      if (!on && !(tok && tok.uncertain && !tok.fixed)) return;
      const b = sym.bbox;
      ctx.strokeStyle = on ? css("--acc", "#0575a6") : css("--warn", "#8a6314");
      ctx.strokeRect(b.x0 * s - 2, b.y0 * s - 2, (b.x1 - b.x0 + 1) * s + 4, (b.y1 - b.y0 + 1) * s + 4);
    });
  }

  fileInput.addEventListener("change", () => {
    const f = fileInput.files && fileInput.files[0];
    fileInput.value = "";
    if (f) readPhoto(f);
  });
  // paste an image anywhere on the Solve tab (text pastes are left alone)
  document.addEventListener("paste", (e) => {
    const solve = document.getElementById("panel-solve");
    if (!solve || solve.hidden || !e.clipboardData) return;
    const text = e.clipboardData.getData("text/plain");
    if (text && text.trim()) return;
    const item = [...(e.clipboardData.items || [])].find((it) => it.kind === "file" && /^image\//.test(it.type));
    const file = item ? item.getAsFile() : [...(e.clipboardData.files || [])].find((f) => /^image\//.test(f.type));
    if (!file) return;
    e.preventDefault();
    readPhoto(file);
  });
  // drag and drop an image onto the problem box
  const hasFiles = (e) => e.dataTransfer && [...(e.dataTransfer.types || [])].includes("Files");
  textarea.addEventListener("dragover", (e) => { if (!hasFiles(e)) return; e.preventDefault(); e.dataTransfer.dropEffect = "copy"; textarea.classList.add("drop"); });
  textarea.addEventListener("dragleave", () => textarea.classList.remove("drop"));
  textarea.addEventListener("drop", (e) => {
    textarea.classList.remove("drop");
    if (!hasFiles(e)) return;
    e.preventDefault();
    const file = [...e.dataTransfer.files].find((f) => /^image\//.test(f.type));
    if (file) readPhoto(file); else toast("Drop an image file to read it");
  });

  // ---------------- review ----------------
  function showResult(V, result) {
    st.result = result;
    st.tokens = V.toEditable(result).map((t) => ({ ...t, original: t.text }));
    st.active = -1;
    st.manual = false;
    st.lastFix = null;
    teach.hidden = true;
    alts.hidden = true;
    if (!result.text) {
      review.hidden = true;
      setStatus(st.mode === "photo" ? "No math was found in this image. Try a sharper, closer photo with the expression filling the frame." : "Nothing was recognized. Try writing larger.", "st-warn");
      redraw();
      updateButtons();
      return;
    }
    review.hidden = false;
    textField.value = result.text;
    const unsure = st.tokens.filter((t) => t.uncertain).length;
    setStatus(unsure ? `Read ${result.symbols.length} symbol${result.symbols.length > 1 ? "s" : ""}; ${unsure} uncertain, highlighted below. Check them before using the text.`
      : `Read ${result.symbols.length} symbol${result.symbols.length > 1 ? "s" : ""}. Check the text before using it.`);
    renderChips();
    renderParse();
    redraw();
    updateButtons();
  }
  function tokenText() { return st.tokens.map((t) => t.text).join(""); }
  function renderChips() {
    chips.classList.toggle("stale", st.manual);
    legend.textContent = st.manual ? "Edited by hand: the symbol chips no longer match the text."
      : st.tokens.some((t) => t.uncertain && !t.fixed) ? "Highlighted symbols are uncertain: select one to see what else it could be."
      : "Select a symbol to see what else it could be.";
    chips.replaceChildren(...st.tokens.map((t, i) => {
      if (t.structural) {
        if (!t.text.trim()) return h("span", { class: "ink-gap", "aria-hidden": "true" });
        return h("span", { class: "ink-struct" + (t.parseError && !st.manual ? " perr" : ""), title: "Layout inserted by the reader", "aria-label": "layout " + t.text }, t.text);
      }
      const pct = Math.round(t.confidence * 100);
      const cls = "ink-chip" + (t.uncertain && !t.fixed ? " unc" : "") + (t.fixed ? " fixed" : "") + (t.parseError && !st.manual ? " perr" : "");
      const label = `${t.text}, ${t.fixed ? "corrected" : pct + " percent confident"}${t.uncertain && !t.fixed ? ", uncertain" : ""}${t.alternatives.length ? ". Show alternatives" : ""}`;
      return h("button", {
        type: "button", class: cls, "aria-label": label, title: t.fixed ? "Corrected" : `${pct}% confident`,
        "aria-expanded": t.alternatives.length ? String(st.active === i) : null, "aria-controls": t.alternatives.length ? "ink-alts" : null,
        disabled: st.manual ? true : null, dataset: { i: String(i) },
        onclick: () => (st.active === i ? closeAlts(true) : openAlts(i)),
      }, t.text);
    }));
  }
  function openAlts(i) {
    const t = st.tokens[i];
    st.active = i;
    alts.id = "ink-alts";
    const choices = [];
    const seen = new Set();
    const add = (text, char, score, current) => {
      if (seen.has(text)) return;
      seen.add(text);
      choices.push(h("button", {
        type: "button", class: "btn small ink-alt" + (current ? " current" : ""), "aria-pressed": String(current),
        onclick: () => pick(i, text, char),
      }, h("span", { class: "mono" }, text), score !== null ? h("span", { class: "tiny muted" }, `${Math.round(score * 100)}%`) : null));
    };
    add(t.text, null, t.fixed ? null : t.confidence, true);
    if (t.fixed && t.original !== t.text) add(t.original, null, null, false);
    for (const a of t.alternatives) add(a.text, a.char, a.score, false);
    alts.replaceChildren(h("span", { class: "tiny muted ink-alts-l" }, t.alternatives.length ? `"${t.text}" could also be:` : `No alternatives for "${t.text}".`), ...choices);
    alts.hidden = false;
    renderChips();
    redraw(); paintPhoto();
    (alts.querySelector(".ink-alt:not(.current)") || alts.querySelector(".ink-alt"))?.focus();
  }
  function closeAlts(focusChip) {
    const i = st.active;
    st.active = -1;
    alts.hidden = true;
    renderChips();
    redraw(); paintPhoto();
    if (focusChip && i >= 0) chips.querySelector(`[data-i="${i}"]`)?.focus();
  }
  function pick(i, text, char) {
    const t = st.tokens[i];
    const changed = t.text !== text;
    t.text = text;
    t.fixed = t.fixed || changed || t.uncertain; // confirming the first reading also clears the warning
    textField.value = tokenText();
    closeAlts(true);
    renderParse();
    updateButtons();
    if (changed && char && st.result.source === "strokes" && t.symbol >= 0) {
      st.lastFix = { char, strokeIds: (st.result.symbols[t.symbol].strokeIds || []).slice() };
      offerTeach();
    }
  }
  function offerTeach() {
    const fix = st.lastFix;
    if (!fix || !fix.strokeIds.length) { teach.hidden = true; return; }
    const shown = fix.char;
    teach.replaceChildren(
      h("span", { class: "small-t" }, `Teach Quelvra your handwriting: remember this as "${shown}" next time?`),
      h("button", { type: "button", class: "btn small", onclick: saveTeach }, icon("plus"), `Remember my "${shown}"`),
      h("button", { type: "button", class: "btn small ghost", onclick: () => { teach.hidden = true; st.lastFix = null; } }, "No thanks"));
    teach.hidden = false;
  }
  async function saveTeach() {
    const fix = st.lastFix;
    if (!fix) return;
    try {
      const V = await vision();
      const group = fix.strokeIds.map((k) => st.strokes[k]).filter(Boolean).map((s) => s.map((p) => ({ x: p.x, y: p.y })));
      V.addTemplate(fix.char, group);
      try { await store.setPref(PREF_TEMPLATES, V.exportTemplates()); } catch (_) { /* still used for this session */ }
      toast(`Saved. Quelvra will use this "${fix.char}" from now on.`);
    } catch (err) {
      toast("Could not save the sample: " + ((err && err.message) || "unknown error"));
    }
    st.lastFix = null;
    teach.hidden = true;
    updateTaught();
    btnUse.focus();
  }
  function renderParse() {
    const text = textField.value.trim();
    if (!text) { parseBox.replaceChildren(); parseBox.className = "ink-parse"; return; }
    let err = null;
    try { if (parse) parse(text); } catch (e) { err = { message: e.message, pos: typeof e.pos === "number" ? e.pos : null, hint: e.hint || "" }; }
    if (err) {
      parseBox.className = "ink-parse err";
      parseBox.replaceChildren(h("div", { class: "err-msg" }, "This text does not parse yet: " + (err.message || "unknown error")), ...syntaxErrorView(text, { pos: err.pos, hint: err.hint }).slice(1),
        h("div", { class: "tiny muted" }, "Fix it here or in the problem box; you can still use it."));
    } else {
      parseBox.className = "ink-parse ok";
      parseBox.replaceChildren(h("span", { class: "st-ok" }, icon("check")), h("span", { class: "small-t" }, "Parses as math."));
    }
  }
  textField.addEventListener("input", () => {
    if (!st.manual && textField.value !== tokenText()) {
      st.manual = true;
      if (st.active >= 0) closeAlts(false);
      renderChips();
      redraw(); paintPhoto();
    } else if (st.manual && textField.value === tokenText()) {
      st.manual = false;
      renderChips();
      redraw(); paintPhoto();
    }
    renderParse();
    updateButtons();
  });
  textField.addEventListener("keydown", (e) => { if (e.key === "Enter") { e.preventDefault(); useText(); } });

  function useText() {
    const text = textField.value.trim();
    if (!text) return;
    close();
    use(text); // fills the problem box and refreshes the preview; never solves
    toast("Recognized text placed in the problem box");
  }

  // ---------------- keyboard ----------------
  panel.addEventListener("keydown", (e) => {
    if (e.key === "Escape") {
      e.preventDefault();
      e.stopPropagation(); // do not also cancel a running solve
      if (!alts.hidden) closeAlts(true);
      else close();
      return;
    }
    if (!alts.hidden && alts.contains(document.activeElement) && (e.key === "ArrowRight" || e.key === "ArrowLeft" || e.key === "ArrowDown" || e.key === "ArrowUp")) {
      const items = [...alts.querySelectorAll(".ink-alt")];
      const k = items.indexOf(document.activeElement);
      const d = e.key === "ArrowRight" || e.key === "ArrowDown" ? 1 : -1;
      e.preventDefault();
      items[(k + d + items.length) % items.length].focus();
    }
  });

  btnDraw.addEventListener("click", () => (st.mode === "draw" ? close() : open("draw")));
  btnPhoto.addEventListener("click", () => fileInput.click());
  window.addEventListener("resize", () => { if (st.mode === "photo") paintPhoto(); });

  return { open, close, readPhoto, state: st };
}
