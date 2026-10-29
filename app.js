/* ==========================================================================
   799325 数字论证器 — 交互逻辑
   依赖同目录 homo.js 提供的 window.homo799325(value) -> string
   ========================================================================== */
(function () {
  "use strict";

  var ENGINE_KEY = "homo799325";
  var DEBOUNCE_MS = 120;
  var COPY_FEEDBACK_MS = 1500;
  var THEME_KEY = "homo799325-theme";
  var PALETTE = { "7": "d7", "9": "d9", "3": "d3", "2": "d2", "5": "d5" };
  var OPERATORS = "+-*/()";
  var GLYPHS = { "-": "\u2212", "*": "\u00d7", "/": "\u00f7" };
  var THEME_ORDER = ["auto", "light", "dark"];
  var THEME_LABELS = { auto: "跟随系统", light: "浅色", dark: "深色" };
  var THEME_ICONS = {
    auto:
      '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="12" r="9"/><path d="M12 3a9 9 0 0 1 0 18Z" fill="currentColor" stroke="none"/></svg>',
    light:
      '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="12" r="4"/><path d="M12 2v2M12 20v2M4.9 4.9l1.4 1.4M17.7 17.7l1.4 1.4M2 12h2M20 12h2M4.9 19.1l1.4-1.4M17.7 6.3l1.4-1.4"/></svg>',
    dark:
      '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M20 14.5A8.5 8.5 0 0 1 9.5 4a8.5 8.5 0 1 0 10.5 10.5Z"/></svg>'
  };

  var fmt = new Intl.NumberFormat("en-US");
  var els = {};
  var state = {
    expr: "",
    runCount: 0,
    expanded: false,
    expandable: false,
    pristine: false,
    timer: 0,
    copyTimer: 0,
    spinTimer: 0,
    theme: "auto"
  };

  function $(selector) {
    return document.querySelector(selector);
  }

  function escapeHtml(text) {
    return String(text).replace(/[&<>"']/g, function (ch) {
      return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[ch];
    });
  }

  /* ---------- expression rendering ---------- */

  function colorize(text) {
    var html = "";
    for (var i = 0; i < text.length; i++) {
      var ch = text.charAt(i);
      if (ch >= "0" && ch <= "9") {
        var tone = PALETTE[ch];
        html += '<span class="d' + (tone ? " " + tone : "") + '">' + ch + "</span>";
      } else if (OPERATORS.indexOf(ch) !== -1) {
        html += '<span class="op">' + (GLYPHS[ch] || ch) + "</span>";
      } else {
        html += '<span class="raw">' + escapeHtml(ch) + "</span>";
      }
    }
    return html;
  }

  function canonicalNumber(text) {
    var n = Number(text);
    return Number.isFinite(n) ? String(n) : text;
  }

  function countBlocks(expr) {
    var digits = expr.replace(/[^0-9]/g, "");
    var count = 0;
    var at = digits.indexOf("799325");
    while (at !== -1) {
      count += 1;
      at = digits.indexOf("799325", at + 6);
    }
    return count;
  }

  /* ---------- stats ---------- */

  function statValue(id, text, idle) {
    var el = document.getElementById(id);
    if (!el) return;
    var b = el.querySelector("b");
    if (b) b.textContent = text;
    el.classList.toggle("is-idle", !!idle);
  }

  function resetStats() {
    statValue("stat-length", "\u2014", true);
    statValue("stat-blocks", "\u2014", true);
  }

  function updateStats(expr) {
    statValue("stat-length", fmt.format(expr.length), false);
    statValue("stat-blocks", fmt.format(countBlocks(expr)), false);
    statValue("stat-runs", fmt.format(state.runCount), false);
  }

  function showEngineMeta() {
    var engine = window[ENGINE_KEY];
    var meta = engine && engine.meta;
    if (!meta) return;
    if (typeof meta.table === "number" && isFinite(meta.table)) {
      statValue("stat-table", fmt.format(meta.table), false);
      var wrap = document.getElementById("stat-table");
      if (wrap && typeof meta.max === "number" && isFinite(meta.max)) {
        wrap.title = "\u5355\u5757\u6700\u5927\u53ef\u8868\u793a\uff1a" + fmt.format(meta.max);
      }
      var howto = document.getElementById("howto-table");
      if (howto) howto.textContent = fmt.format(meta.table);
    }
  }

  /* ---------- states ---------- */

  function setStatus(text) {
    if (els.status) els.status.textContent = text || "";
  }

  function renderEmpty() {
    state.expr = "";
    state.expanded = false;
    els.result.innerHTML =
      '<div class="state-empty">' +
      '<div class="empty-mark" aria-hidden="true">' +
      colorize("799325") +
      '<span class="empty-arrow">\u2192</span><span class="empty-q">?</span></div>' +
      '<p class="empty-title">\u8f93\u5165\u4e00\u4e2a\u6570\u5b57</p>' +
      '<p class="empty-hint">\u8fd9\u4e32\u6570\u5b57\u53ea\u7531 7 9 9 3 2 5 \u7ec4\u6210\uff0c\u5374\u80fd\u8bba\u8bc1\u51fa 2024\u3001-7\uff0c\u751a\u81f3 3.14\u3002</p>' +
      "</div>";
    els.copy.disabled = true;
    resetCopyFeedback();
    resetStats();
    setStatus("\u8bf7\u8f93\u5165\u4e00\u4e2a\u6570\u5b57");
  }

  function renderError(message) {
    state.expr = "";
    state.expanded = false;
    els.result.innerHTML =
      '<div class="state-error" role="alert">' +
      '<span class="error-badge" aria-hidden="true">!</span>' +
      '<div class="error-body">' +
      '<p class="error-title">\u8bba\u8bc1\u5931\u8d25</p>' +
      '<p class="error-msg">' + escapeHtml(message) + "</p>" +
      "</div></div>";
    els.copy.disabled = true;
    resetCopyFeedback();
    resetStats();
    setStatus("\u8bba\u8bc1\u5931\u8d25\uff1a" + message);
  }

  function renderResult(display, expr) {
    state.expr = expr;
    state.expanded = false;
    els.result.innerHTML =
      '<div class="equation">' +
      '<span class="eq-number">' + colorize(display) + "</span>" +
      '<span class="eq-sign">=</span>' +
      "</div>" +
      '<div class="expr-scroll" id="expr-scroll">' +
      '<div class="expr">' + colorize(expr) + "</div>" +
      "</div>" +
      '<button class="expand" id="expand" type="button" aria-expanded="false" hidden>' +
      '<span class="expand-label">\u5c55\u5f00\u5168\u90e8</span>' +
      '<svg class="expand-chevron" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="m6 9 6 6 6-6"/></svg>' +
      "</button>";
    els.copy.disabled = false;
    resetCopyFeedback();
    setStatus(
      "\u5df2\u8bba\u8bc1 " + display + "\uff1a\u8868\u8fbe\u5f0f\u5171 " +
      fmt.format(expr.length) + " \u4e2a\u5b57\u7b26"
    );
    window.requestAnimationFrame(syncExpand);
  }

  /* ---------- long expression folding ---------- */

  function collapseHeight() {
    var raw = window.getComputedStyle(document.documentElement).getPropertyValue("--expr-collapse");
    var value = parseFloat(raw);
    return isFinite(value) ? value : 240;
  }

  function syncExpand() {
    var scroll = document.getElementById("expr-scroll");
    var btn = document.getElementById("expand");
    if (!scroll || !btn) {
      state.expandable = false;
      return;
    }
    var expanded = state.expanded;
    var natural = scroll.scrollHeight;
    var clipped = !expanded && natural > collapseHeight() + 1;
    scroll.classList.toggle("is-expanded", expanded);
    scroll.classList.toggle("is-clamped", clipped);
    state.expandable = clipped || expanded;
    btn.hidden = !state.expandable;
    btn.classList.toggle("is-open", expanded);
    btn.setAttribute("aria-expanded", expanded ? "true" : "false");
    var label = btn.querySelector(".expand-label");
    if (label) label.textContent = expanded ? "\u6536\u8d77" : "\u5c55\u5f00\u5168\u90e8";
  }

  function toggleExpand() {
    if (!state.expandable) return;
    state.expanded = !state.expanded;
    syncExpand();
  }

  /* ---------- copy ---------- */

  function resetCopyFeedback() {
    if (state.copyTimer) {
      window.clearTimeout(state.copyTimer);
      state.copyTimer = 0;
    }
    if (!els.copy) return;
    els.copy.classList.remove("is-copied", "is-failed");
    var label = els.copy.querySelector(".btn-label");
    if (label) label.textContent = "\u590d\u5236";
  }

  function flashCopy(ok) {
    if (state.copyTimer) window.clearTimeout(state.copyTimer);
    els.copy.classList.toggle("is-copied", ok);
    els.copy.classList.toggle("is-failed", !ok);
    var label = els.copy.querySelector(".btn-label");
    if (label) label.textContent = ok ? "\u5df2\u590d\u5236" : "\u590d\u5236\u5931\u8d25";
    state.copyTimer = window.setTimeout(function () {
      state.copyTimer = 0;
      els.copy.classList.remove("is-copied", "is-failed");
      if (label) label.textContent = "\u590d\u5236";
    }, COPY_FEEDBACK_MS);
  }

  function legacyCopy(text) {
    var area = document.createElement("textarea");
    area.value = text;
    area.setAttribute("readonly", "");
    area.style.position = "fixed";
    area.style.top = "0";
    area.style.left = "-9999px";
    area.style.opacity = "0";
    document.body.appendChild(area);
    var ok = false;
    try {
      area.select();
      area.setSelectionRange(0, text.length);
      ok = document.execCommand("copy");
    } catch (err) {
      ok = false;
    }
    document.body.removeChild(area);
    return ok;
  }

  function copyExpression() {
    if (!state.expr) return;
    var text = state.expr;

    function done(ok) {
      flashCopy(ok);
    }

    if (navigator.clipboard && typeof navigator.clipboard.writeText === "function") {
      navigator.clipboard.writeText(text).then(
        function () {
          done(true);
        },
        function () {
          done(legacyCopy(text));
        }
      );
    } else {
      done(legacyCopy(text));
    }
  }

  /* ---------- engine ---------- */

  function evaluate(rawValue) {
    if (state.timer) {
      window.clearTimeout(state.timer);
      state.timer = 0;
    }
    var trimmed = String(rawValue == null ? "" : rawValue).trim();
    els.clear.hidden = trimmed === "";

    if (!trimmed) {
      renderEmpty();
      return false;
    }

    var engine = window[ENGINE_KEY];
    if (typeof engine !== "function") {
      renderError("\u8bba\u8bc1\u5f15\u64ce\u8fd8\u6ca1\u52a0\u8f7d\u597d\u3002\u8bf7\u786e\u8ba4 homo.js \u4e0e index.html \u5728\u540c\u4e00\u76ee\u5f55\u3002");
      return false;
    }

    var display = canonicalNumber(trimmed);
    var expr;
    try {
      expr = engine(display);
    } catch (err) {
      var message = err && err.message ? String(err.message) : "\u8fd9\u4e2a\u6570\u5b57\u6682\u65f6\u65e0\u6cd5\u8bba\u8bc1\u3002";
      renderError(message);
      return false;
    }

    if (typeof expr !== "string" || expr.trim() === "") {
      renderError("\u5f15\u64ce\u6ca1\u6709\u8fd4\u56de\u6709\u6548\u8868\u8fbe\u5f0f\uff0c\u8bf7\u6362\u4e00\u4e2a\u6570\u5b57\u8bd5\u8bd5\u3002");
      return false;
    }

    expr = expr.trim();
    state.runCount += 1;
    renderResult(display, expr);
    updateStats(expr);
    return true;
  }

  function canEvaluate(value) {
    var engine = window[ENGINE_KEY];
    if (typeof engine !== "function") return false;
    try {
      var expr = engine(canonicalNumber(value));
      return typeof expr === "string" && expr.trim() !== "";
    } catch (err) {
      return false;
    }
  }

  /* ---------- random ---------- */

  function randomValue() {
    if (Math.random() < 0.22) {
      var whole = Math.floor(Math.random() * 2000) - 1000;
      var decimals = 1 + Math.floor(Math.random() * 4);
      var frac = Math.floor(Math.random() * Math.pow(10, decimals));
      if (frac === 0 && whole === 0) frac = 1;
      var sign = whole === 0 && Math.random() < 0.5 ? "-" : "";
      return sign + String(whole) + "." + String(frac).padStart(decimals, "0");
    }
    var magnitude = Math.pow(10, 1 + Math.floor(Math.random() * 6));
    var value = Math.floor(Math.random() * magnitude);
    if (value === 0) value = 1;
    if (Math.random() < 0.25) value = -value;
    return String(value);
  }

  function randomize() {
    var candidate = "2024";
    for (var attempt = 0; attempt < 8; attempt++) {
      var next = randomValue();
      if (canEvaluate(next)) {
        candidate = next;
        break;
      }
    }
    els.number.value = candidate;
    els.clear.hidden = false;
    evaluate(candidate);
    els.random.classList.add("is-spinning");
    window.clearTimeout(state.spinTimer);
    state.spinTimer = window.setTimeout(function () {
      els.random.classList.remove("is-spinning");
    }, 520);
  }

  /* ---------- input ---------- */

  function setInput(value) {
    els.number.value = value;
    els.clear.hidden = String(value).trim() === "";
    evaluate(value);
  }

  function clearInput() {
    setInput("");
    try {
      els.number.focus({ preventScroll: true });
    } catch (err) {
      els.number.focus();
    }
  }

  /* ---------- theme ---------- */

  function readTheme() {
    try {
      var saved = window.localStorage.getItem(THEME_KEY);
      if (saved === "light" || saved === "dark") return saved;
    } catch (err) {
      /* file:// 下可能禁用 localStorage */
    }
    return "auto";
  }

  function applyTheme(mode, persist) {
    state.theme = mode;
    document.documentElement.setAttribute("data-theme", mode);
    if (els.theme) {
      els.theme.innerHTML = THEME_ICONS[mode];
      els.theme.setAttribute("aria-label", "\u4e3b\u9898\uff1a" + THEME_LABELS[mode] + "\uff08\u70b9\u51fb\u5207\u6362\uff09");
      els.theme.title = "\u4e3b\u9898\uff1a" + THEME_LABELS[mode];
    }
    if (!persist) return;
    try {
      if (mode === "auto") window.localStorage.removeItem(THEME_KEY);
      else window.localStorage.setItem(THEME_KEY, mode);
    } catch (err) {
      /* ignore */
    }
  }

  function cycleTheme() {
    var index = THEME_ORDER.indexOf(state.theme);
    applyTheme(THEME_ORDER[(index + 1) % THEME_ORDER.length], true);
  }

  /* ---------- boot ---------- */

  function cacheElements() {
    els.number = document.getElementById("number");
    els.clear = document.getElementById("clear");
    els.random = document.getElementById("random");
    els.copy = document.getElementById("copy");
    els.chips = document.getElementById("chips");
    els.theme = document.getElementById("theme");
    els.result = document.getElementById("result");
    els.status = document.getElementById("result-status");
  }

  function bindEvents() {
    els.number.addEventListener("input", function () {
      state.pristine = false;
      els.clear.hidden = els.number.value.trim() === "";
      if (state.timer) window.clearTimeout(state.timer);
      state.timer = window.setTimeout(function () {
        state.timer = 0;
        evaluate(els.number.value);
      }, DEBOUNCE_MS);
    });

    els.number.addEventListener("keydown", function (event) {
      if (state.pristine && !event.ctrlKey && !event.metaKey && !event.altKey) {
        if (event.key.length === 1 || event.key === "Backspace" || event.key === "Delete") {
          els.number.select();
          state.pristine = false;
        }
      }
      if (event.key === "Enter") {
        event.preventDefault();
        evaluate(els.number.value);
      } else if (event.key === "Escape") {
        event.preventDefault();
        clearInput();
      }
    });

    els.clear.addEventListener("click", clearInput);

    els.random.addEventListener("click", randomize);

    els.copy.addEventListener("click", copyExpression);

    els.chips.addEventListener("click", function (event) {
      var chip = event.target.closest(".chip");
      if (!chip) return;
      setInput(chip.getAttribute("data-value") || "");
    });

    els.result.addEventListener("click", function (event) {
      var btn = event.target.closest("#expand");
      if (btn) toggleExpand();
    });

    els.theme.addEventListener("click", cycleTheme);

    var resizeTimer = 0;
    window.addEventListener("resize", function () {
      window.clearTimeout(resizeTimer);
      resizeTimer = window.setTimeout(syncExpand, 160);
    });

    window.addEventListener("load", function () {
      syncExpand();
      try {
        if (document.activeElement === document.body || document.activeElement === els.number) {
          els.number.focus({ preventScroll: true });
          var end = els.number.value.length;
          els.number.setSelectionRange(end, end);
        }
      } catch (err) {
        /* ignore */
      }
    });

    if (document.fonts && document.fonts.ready && typeof document.fonts.ready.then === "function") {
      document.fonts.ready.then(function () {
        syncExpand();
      });
    }
  }

  function boot() {
    cacheElements();
    if (!els.number || !els.result) return;
    bindEvents();
    applyTheme(readTheme(), false);
    showEngineMeta();
    setInput("2024");
    state.pristine = true;
    try {
      els.number.focus({ preventScroll: true });
      var end = els.number.value.length;
      els.number.setSelectionRange(end, end);
    } catch (err) {
      els.number.focus();
    }
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", boot);
  } else {
    boot();
  }
})();
