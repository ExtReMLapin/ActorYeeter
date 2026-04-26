// ==UserScript==
// @name         Prime Video — Actor Yeeter (auto-skip via X-Ray)
// @namespace    https://primevideo.com/userscripts
// @version      0.3.0
// @description  Automatically skips scenes featuring blacklisted actors, using the X-Ray data prefetched by the player.
// @author       you
// @match        *://*.primevideo.com/*
// @match        *://*.amazon.com/gp/video/*
// @match        *://*.amazon.com/Amazon-Video/*
// @match        *://*.amazon.com/-/*/dp/*
// @match        *://*.amazon.fr/*video*
// @match        *://*.amazon.de/*video*
// @match        *://*.amazon.co.uk/*video*
// @run-at       document-start
// @grant        none
// ==/UserScript==
//
// Notes (observed live on primevideo.com region/eu):
//   - The X-Ray payload is delivered in a single XHR to
//     https://atv-ps-eu.primevideo.com/swift/page/xrayVOD?... (~280 kB).
//   - That request is issued from the `#starlight-iframe` iframe
//     (loaded from primevideo.com/gp/video/salp/i?token=...).
//     The userscript therefore has to run inside THAT iframe too: we
//     don't set @noframes and our @match covers both URLs, so
//     Tampermonkey injects in both contexts automatically.
//   - JSON response shape:
//        page.sections.{left|center|bottom}.widgets.widgetList[].widgets.widgetList[]
//        .items[]                  -> catalog [{id:"/name/nm.../Char", item:{textMap:{PRIMARY:"Actor",TERTIARY:"Character"}, imageMap...}}]
//        .partitionedChangeList[]  -> [{timeRange:{startTime,endTime}, changesCollection:[{changeType:"AddItem", itemId:"/name/nm.../Char", timePosition}]}]
//     Every change observed so far is an "AddItem": an actor listed in a
//     partition is considered present for the whole partition timeRange.
//   - All timestamps are in MILLISECONDS.
//
// Architecture:
//   - The script runs in BOTH the parent frame and the iframe.
//   - It hooks fetch + XMLHttpRequest.prototype.open in each context
//     (so it captures any response that looks like X-Ray data).
//   - Each context drives its own <video> (skip engine is local).
//   - The blacklist + the detected cast are shared via localStorage,
//     synchronized across frames with a BroadcastChannel ('pvAB').
//   - The floating UI is rendered only in the top frame.

/* eslint-disable no-console */
(function () {
  'use strict';

  // ──────────────────────────────────────────────────────────────────────────
  //  Constants & helpers
  // ──────────────────────────────────────────────────────────────────────────
  const NS = 'pvAB';                     // namespace for CSS classes & DOM ids
  const LS_KEY = 'pvAB.blacklist.v1';    // localStorage key: [{imdbId, name}]
  const LS_CAST_KEY = 'pvAB.cast.v1';    // last detected cast (UI cache)
  const LS_OPTS_KEY = 'pvAB.options.v1'; // { enabled: bool }
  const IS_TOP = (function () { try { return window.top === window; } catch (_) { return false; } })();
  const FRAME_TAG = IS_TOP ? 'top' : 'frame';
  const LOG = (...a) => console.log('%c[pvAB:' + FRAME_TAG + ']', 'color:#5c8dff', ...a);
  const WARN = (...a) => console.warn('[pvAB:' + FRAME_TAG + ']', ...a);
  /** @type {BroadcastChannel|null} */
  let bc = null;
  try { bc = new BroadcastChannel('pvAB'); } catch (_) { bc = null; }

  // ──────────────────────────────────────────────────────────────────────────
  //  Global state
  // ──────────────────────────────────────────────────────────────────────────
  /** @type {Array<{start:number,end:number,ids:Set<string>}>}
   *  segments sorted by start (in ms) */
  let segments = [];
  /** @type {Map<string,{name:string,character:string|null,image:string|null}>} */
  let idToInfo = new Map();
  /** @type {boolean} whether the X-Ray timestamps are in milliseconds */
  let timesAreMs = true;
  /** Last segment we actually skipped (used to break out of skip loops). */
  let lastSkippedSegment = null;

  // ──────────────────────────────────────────────────────────────────────────
  //  Storage
  // ──────────────────────────────────────────────────────────────────────────
  function loadBlacklist() {
    try {
      const raw = localStorage.getItem(LS_KEY);
      if (!raw) return [];
      const arr = JSON.parse(raw);
      return Array.isArray(arr) ? arr.filter(e => e && e.imdbId) : [];
    } catch { return []; }
  }
  function saveBlacklist(list, opts) {
    localStorage.setItem(LS_KEY, JSON.stringify(list));
    if (!opts || opts.refresh !== false) refreshUI();
    else updateStats();
  }
  function updateStats() {
    if (!panelEl) return;
    const cast = getDisplayCast();
    const blN = loadBlacklist().length;
    const el = panelEl.querySelector(`#${NS}-stats`);
    if (el) el.textContent = `${segments.length} segments · ${cast.length} actors detected · ${blN} blocked`;
  }
  function loadOpts() {
    try { return Object.assign({ enabled: true }, JSON.parse(localStorage.getItem(LS_OPTS_KEY) || '{}')); }
    catch { return { enabled: true }; }
  }
  function saveOpts(opts) {
    localStorage.setItem(LS_OPTS_KEY, JSON.stringify(opts));
  }
  function blacklistedSet() {
    return new Set(loadBlacklist().map(e => e.imdbId));
  }

  // ──────────────────────────────────────────────────────────────────────────
  //  Network interception (fetch + XHR), installed before the player runs
  // ──────────────────────────────────────────────────────────────────────────
  // --- fetch hook ---
  const origFetch = window.fetch;
  window.fetch = function (input, init) {
    const url = (typeof input === 'string') ? input : (input && input.url) || '';
    const p = origFetch.apply(this, arguments);
    p.then(res => {
      try {
        // Clone so we don't consume the body the page wants to read.
        res.clone().text().then(body => maybeIngestJson(body, res.url || url)).catch(() => {});
      } catch { /* ignore */ }
    }, () => {});
    return p;
  };

  // --- XHR hook (prototype-level: also covers XHRs created before us) ---
  const xhrProto = window.XMLHttpRequest && window.XMLHttpRequest.prototype;
  if (xhrProto && !xhrProto.__pvABHooked) {
    xhrProto.__pvABHooked = true;
    const origOpen = xhrProto.open;
    xhrProto.open = function (method, url) {
      this.__pvABUrl = url || '';
      this.addEventListener('load', () => {
        try {
          const body = (this.responseType === '' || this.responseType === 'text') ? this.responseText : null;
          if (body) maybeIngestJson(body, this.__pvABUrl);
        } catch { /* ignore */ }
      });
      return origOpen.apply(this, arguments);
    };
  }

  // ──────────────────────────────────────────────────────────────────────────
  //  "Does this look like X-Ray?" detection + parsing
  // ──────────────────────────────────────────────────────────────────────────
  // Quick heuristic: look for an IMDb id /name/nmXXXXX and a timeRange.
  const NAME_ID_RE = /\/?name\/(nm\d{5,12})/;
  const HAS_NAME_RE = /\/name\/nm\d{5,12}/;
  const HAS_TIMERANGE_RE = /"(?:timeRange|startTime)"\s*:/;
  const URL_HINT_RE = /\/swift\/page\/xrayVOD|xrayVOD\?|\/xray\//i;

  function maybeIngestJson(text, url) {
    if (!text || text.length < 300) return;
    const urlHint = URL_HINT_RE.test(url || '');
    // Accept if the URL is a known X-Ray endpoint OR if the body matches.
    if (!urlHint && (!HAS_NAME_RE.test(text) || !HAS_TIMERANGE_RE.test(text))) return;
    let json;
    try { json = JSON.parse(text); } catch { return; }
    LOG('X-Ray candidate intercepted:', (url || '(inline)').slice(0, 120), '— size=', text.length);
    ingest(json);
  }

  // pickName: try to pull a human-readable label out of a node
  function pickText(v) {
    if (v == null) return null;
    if (typeof v === 'string') return v;
    if (typeof v === 'object') {
      return v.text || v.value || v.string || v.displayString || v.PRIMARY || null;
    }
    return null;
  }
  // True if the node is the canonical "actor" item. On xrayVOD several sub-cards
  // ("Date of birth", "View biography", "Known for...") share the same
  // analytics.itemType="Actor", so we need a stricter condition:
  //   - blueprint.blueprintItemType === 'inSceneActor', OR
  //   - id ends with /name/nm.../<Character> (with no leading '_').
  function isActorItem(node) {
    const it = node && (node.item || node);
    if (!it) return false;
    const bpType = it.blueprint && it.blueprint.blueprintItemType;
    if (bpType === 'inSceneActor') return true;
    const id = it.id || node.id;
    if (typeof id === 'string') {
      const m = id.match(/^\/?name\/nm\d+\/([^/]*)$/);
      if (m && m[1] && !m[1].startsWith('_')) {
        // The id points at the main character card (not a sub-attribute).
        const t = it.analytics && it.analytics.local && it.analytics.local.itemType;
        if (t === 'Actor') return true;
      }
    }
    return false;
  }
  function pickName(node) {
    // xrayVOD shape: item.textMap.PRIMARY = actor name,
    // but ONLY on the canonical "Actor" node.
    if (isActorItem(node)) {
      const tm = (node.item && node.item.textMap) || node.textMap;
      if (tm && typeof tm.PRIMARY === 'string') return tm.PRIMARY;
    }
    return pickText(node.title) || pickText(node.heading) || pickText(node.displayName)
        || pickText(node.name) || pickText(node.primaryText) || pickText(node.text)
        || (typeof node.label === 'string' ? node.label : null);
  }
  function pickCharacter(node) {
    if (isActorItem(node)) {
      const tm = (node.item && node.item.textMap) || node.textMap;
      if (tm && typeof tm.TERTIARY === 'string') return tm.TERTIARY;
    }
    return null;
  }
  function pickImage(node) {
    if (!node) return null;
    // imageMap.PRIMARY.url (xrayVOD)
    if (node.imageMap && node.imageMap.PRIMARY && node.imageMap.PRIMARY.url) return node.imageMap.PRIMARY.url;
    if (node.item && node.item.imageMap && node.item.imageMap.PRIMARY && node.item.imageMap.PRIMARY.url) return node.item.imageMap.PRIMARY.url;
    const i = node.image || node.picture || node.thumbnail || node.imageUrl;
    if (!i) return null;
    if (typeof i === 'string') return i;
    return i.url || i.src || null;
  }

  function collectNmIds(root, out) {
    (function walk(n) {
      if (!n) return;
      if (typeof n === 'string') {
        const m = n.match(NAME_ID_RE);
        if (m) out.add(m[1]);
        return;
      }
      if (Array.isArray(n)) { for (const x of n) walk(x); return; }
      if (typeof n !== 'object') return;
      // Common case: { id: "/name/nmXXX/Char" }
      const id = n.id || n.entityId || n.itemId;
      if (typeof id === 'string') {
        const m = id.match(NAME_ID_RE);
        if (m) out.add(m[1]);
      }
      for (const k in n) walk(n[k]);
    })(root);
  }

  function ingest(root) {
    // A full xrayVOD payload is self-contained for the current title:
    // wipe previous state so we never accumulate cast/segments across titles.
    idToInfo = new Map();
    segments = [];
    lastSkippedSegment = null;
    const nameByNm = idToInfo;
    const segs = [];

    (function walk(n) {
      if (!n) return;
      if (Array.isArray(n)) { for (const x of n) walk(x); return; }
      if (typeof n !== 'object') return;

      // 1) Catalog lookup from a "person" node
      const id = n.id || n.entityId || n.itemId;
      if (typeof id === 'string') {
        const m = id.match(NAME_ID_RE);
        if (m) {
          const nm = m[1];
          const realName = pickName(n);
          // Character name: encoded in the id, or in a sub-text field
          let character = null;
          // /name/nmXXX/Char%20Name
          const slashed = id.split('/');
          if (slashed.length >= 4 && slashed[3]) {
            character = decodeURIComponent(slashed[3]).replace(/[+_]/g, ' ');
          }
          const sub = pickText(n.subText) || pickText(n.subtitle) || pickText(n.secondaryText);
          if (sub && /^as\s+/i.test(sub)) character = sub.replace(/^as\s+/i, '');
          const img = pickImage(n);
          const cur = nameByNm.get(nm) || { name: null, character: null, image: null };
          // pickName only returns a name on the canonical actor node,
          // so the first value we get is the correct one.
          if (realName && !cur.name) cur.name = realName;
          if (character && !cur.character) cur.character = character;
          if (img && !cur.image) cur.image = img;
          nameByNm.set(nm, cur);
        }
      }

      // 2) Time range detection
      let tr = null;
      if (n.timeRange && typeof n.timeRange === 'object') tr = n.timeRange;
      else if (typeof n.startTime === 'number' && typeof n.endTime === 'number') tr = n;

      if (tr && Number.isFinite(tr.startTime) && Number.isFinite(tr.endTime) && tr.endTime > tr.startTime) {
        const ids = new Set();
        // Canonical xrayVOD shape: the partition has a `changesCollection` with
        // itemId values pointing at /name/nm…. That is the ONLY reliable
        // source of presence info here.
        if (Array.isArray(n.changesCollection)) {
          for (const c of n.changesCollection) {
            if (c && typeof c.itemId === 'string') {
              const m = c.itemId.match(NAME_ID_RE);
              if (m) ids.add(m[1]);
            }
          }
        } else {
          // Fallback: different X-Ray shape, gather every nm in the subtree.
          collectNmIds(n, ids);
        }
        if (ids.size) {
          segs.push({ start: +tr.startTime, end: +tr.endTime, ids });
        }
      }

      for (const k in n) walk(n[k]);
    })(root);

    if (!segs.length) return;

    // Sort + dedupe (the same scenes appear in several X-Ray sections).
    segs.sort((a, b) => a.start - b.start || a.end - b.end);
    const dedup = [];
    let last = null;
    for (const s of segs) {
      const sig = s.start + '_' + s.end + '_' + [...s.ids].sort().join(',');
      if (last !== sig) { dedup.push(s); last = sig; }
    }
    segments = dedup;
    // ms vs s detection: if max endTime > 36000 (10h in s) it must be ms.
    const maxEnd = segs[segs.length - 1].end;
    timesAreMs = maxEnd > 36000;
    LOG('X-Ray indexed →', segs.length, 'segments,', nameByNm.size, 'distinct actors.',
        'unit=', timesAreMs ? 'ms' : 's');

    // Cache & broadcast: the detected cast is consumed by the UI in the top frame.
    publishCast();
    // If playback is already running, (re)bind the skip engine.
    bindToVideo();
    refreshUI();
  }

  function publishCast() {
    // Flatten idToInfo into a plain array.
    const arr = [];
    for (const [imdbId, info] of idToInfo) {
      if (!info || !info.name) continue;
      arr.push({ imdbId, name: info.name, character: info.character || null, image: info.image || null });
    }
    arr.sort((a, b) => a.name.localeCompare(b.name));
    // Local cache (read by other frames if no BroadcastChannel is available).
    try { localStorage.setItem(LS_CAST_KEY, JSON.stringify({ ts: Date.now(), cast: arr })); } catch (_) {}
    // BroadcastChannel for the top frame.
    if (bc) try { bc.postMessage({ type: 'cast', cast: arr }); } catch (_) {}
  }

  // ──────────────────────────────────────────────────────────────────────────
  //  Skip engine
  // ──────────────────────────────────────────────────────────────────────────
  let boundVideo = null;
  let lastTickAt = 0;

  function findActiveVideo() {
    const vids = Array.from(document.querySelectorAll('video'));
    // Prefer a non-muted, non-finished video with a plausible duration.
    let best = null;
    for (const v of vids) {
      if (!isFinite(v.duration) || v.duration <= 0) continue;
      if (!best || (v.currentTime > 0 && v.duration > best.duration)) best = v;
    }
    return best || vids[0] || null;
  }

  function bindToVideo() {
    const v = findActiveVideo();
    if (!v || v === boundVideo) return;
    boundVideo = v;
    v.addEventListener('timeupdate', onTimeUpdate, { passive: true });
    v.addEventListener('seeked', () => { lastSkippedSegment = null; }, { passive: true });
    LOG('Video element bound, skip engine active.');
  }

  function currentTimeInUnit(video) {
    return timesAreMs ? video.currentTime * 1000 : video.currentTime;
  }
  function setTimeFromUnit(video, t) {
    video.currentTime = timesAreMs ? t / 1000 : t;
  }

  function findSegmentAt(t) {
    // Binary search on start, then verify end.
    let lo = 0, hi = segments.length - 1, found = null;
    while (lo <= hi) {
      const mid = (lo + hi) >> 1;
      const s = segments[mid];
      if (t < s.start) hi = mid - 1;
      else if (t > s.end) lo = mid + 1;
      else { found = s; break; }
    }
    return found;
  }

  function onTimeUpdate(e) {
    const v = e.currentTarget;
    if (!segments.length) return;
    const opts = loadOpts();
    if (!opts.enabled) return;
    const now = performance.now();
    if (now - lastTickAt < 200) return;
    lastTickAt = now;

    const t = currentTimeInUnit(v);
    const seg = findSegmentAt(t);
    if (!seg) { lastSkippedSegment = null; return; }
    if (seg === lastSkippedSegment) return;
    const bl = blacklistedSet();
    if (!bl.size) return;

    // Intersection
    let hitId = null;
    for (const id of seg.ids) if (bl.has(id)) { hitId = id; break; }
    if (!hitId) return;

    const info = idToInfo.get(hitId) || { name: hitId };
    const offset = timesAreMs ? 50 : 0.05;
    const target = seg.end + offset;
    LOG('Skip →', info.name || hitId, '   segment=[', seg.start, '..', seg.end, ']');
    lastSkippedSegment = seg;
    setTimeFromUnit(v, target);
    showToast(`Auto-skip · ${info.name || hitId}`);
  }

  // ──────────────────────────────────────────────────────────────────────────
  //  UI: floating panel
  // ──────────────────────────────────────────────────────────────────────────
  function injectStyles() {
    const css = `
    .${NS}-fab{position:fixed;top:14px;right:14px;z-index:2147483647;
      width:34px;height:34px;border-radius:50%;background:#0e1726;color:#cfe;
      box-shadow:0 2px 12px rgba(0,0,0,.45);display:flex;align-items:center;
      justify-content:center;cursor:pointer;font:600 14px/1 system-ui,Segoe UI,sans-serif;
      border:1px solid #1d2c44;user-select:none;opacity:.85;transition:opacity .15s}
    .${NS}-fab:hover{opacity:1}
    .${NS}-fab.${NS}-disabled{background:#3a1010;color:#fbb}
    .${NS}-panel{position:fixed;top:54px;right:14px;z-index:2147483647;
      width:340px;max-height:72vh;background:#0e1726;color:#dde6f5;
      border:1px solid #1d2c44;border-radius:10px;box-shadow:0 8px 28px rgba(0,0,0,.5);
      font:13px/1.4 system-ui,Segoe UI,sans-serif;display:none;flex-direction:column;overflow:hidden}
    .${NS}-panel.${NS}-open{display:flex}
    .${NS}-head{display:flex;align-items:center;justify-content:space-between;padding:10px 12px;border-bottom:1px solid #1d2c44}
    .${NS}-head h3{margin:0;font:600 13px/1 system-ui;color:#fff}
    .${NS}-tabs{display:flex;border-bottom:1px solid #1d2c44}
    .${NS}-tab{flex:1;padding:8px;text-align:center;cursor:pointer;color:#8aa}
    .${NS}-tab.${NS}-active{color:#fff;border-bottom:2px solid #5c8dff}
    .${NS}-body{flex:1;overflow:auto;padding:8px 10px}
    .${NS}-row{display:flex;align-items:center;gap:8px;padding:6px 4px;border-bottom:1px dashed #1d2c44}
    .${NS}-row:last-child{border-bottom:0}
    .${NS}-row img{width:28px;height:28px;border-radius:50%;object-fit:cover;background:#1d2c44}
    .${NS}-row .${NS}-meta{flex:1;min-width:0}
    .${NS}-row .${NS}-name{color:#fff;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
    .${NS}-row .${NS}-char{color:#8aa;font-size:11px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
    .${NS}-btn{background:#1d2c44;color:#dde6f5;border:0;padding:5px 8px;border-radius:5px;cursor:pointer;font:600 11px/1 system-ui}
    .${NS}-btn:hover{background:#2a3e5e}
    .${NS}-btn.${NS}-danger{background:#3a1010;color:#fbb}
    .${NS}-btn.${NS}-danger:hover{background:#5c1818}
    .${NS}-btn.${NS}-active{background:#0d3a1a;color:#bfe9c8}
    .${NS}-foot{padding:8px 12px;border-top:1px solid #1d2c44;display:flex;gap:8px;align-items:center;font-size:11px;color:#8aa}
    .${NS}-toggle{display:flex;align-items:center;gap:6px;cursor:pointer}
    .${NS}-empty{color:#8aa;text-align:center;padding:18px 8px;font-style:italic}
    .${NS}-toast{position:fixed;left:50%;bottom:88px;transform:translateX(-50%);
      z-index:2147483647;background:#0e1726cc;color:#fff;border:1px solid #1d2c44;
      padding:8px 14px;border-radius:6px;font:600 13px/1 system-ui;
      backdrop-filter:blur(6px);transition:opacity .25s;pointer-events:none}
    .${NS}-add{display:flex;gap:6px;margin:6px 0 10px}
    .${NS}-add input{flex:1;background:#0a1320;border:1px solid #1d2c44;color:#dde6f5;
      padding:6px 8px;border-radius:5px;font:13px/1.2 system-ui}
    `;
    const s = document.createElement('style');
    s.id = `${NS}-styles`;
    s.textContent = css;
    document.documentElement.appendChild(s);
  }

  let panelEl = null, fabEl = null, currentTab = 'blacklist';

  function buildUI() {
    if (fabEl) return;
    injectStyles();

    fabEl = document.createElement('div');
    fabEl.className = `${NS}-fab`;
    fabEl.title = 'Prime Video Actor Yeeter';
    fabEl.textContent = '⛔';
    fabEl.addEventListener('click', () => {
      panelEl.classList.toggle(`${NS}-open`);
      refreshUI();
    });
    document.body.appendChild(fabEl);

    panelEl = document.createElement('div');
    panelEl.className = `${NS}-panel`;
    panelEl.innerHTML = `
      <div class="${NS}-head">
        <h3>Actor Yeeter</h3>
        <span class="${NS}-toggle">
          <input type="checkbox" id="${NS}-enabled">
          <label for="${NS}-enabled">auto-skip</label>
        </span>
      </div>
      <div class="${NS}-tabs">
        <div class="${NS}-tab ${NS}-active" data-tab="blacklist">Blacklist</div>
        <div class="${NS}-tab" data-tab="cast">Detected cast</div>
      </div>
      <div class="${NS}-body" id="${NS}-body"></div>
      <div class="${NS}-foot">
        <span id="${NS}-stats">—</span>
      </div>
    `;
    document.body.appendChild(panelEl);

    panelEl.querySelectorAll(`.${NS}-tab`).forEach(t => {
      t.addEventListener('click', () => {
        currentTab = t.dataset.tab;
        panelEl.querySelectorAll(`.${NS}-tab`).forEach(x =>
          x.classList.toggle(`${NS}-active`, x === t));
        refreshUI();
      });
    });

    const chk = panelEl.querySelector(`#${NS}-enabled`);
    chk.checked = loadOpts().enabled;
    chk.addEventListener('change', () => {
      const o = loadOpts(); o.enabled = chk.checked; saveOpts(o);
      fabEl.classList.toggle(`${NS}-disabled`, !chk.checked);
    });
    fabEl.classList.toggle(`${NS}-disabled`, !chk.checked);
  }

  function rowFor(actor, action) {
    const r = document.createElement('div');
    r.className = `${NS}-row`;
    // Build children imperatively so we can attach loading="lazy" attribute,
    // which prevents 100+ image fetches firing at once on a big cast.
    const img = document.createElement('img');
    if (actor.image) img.src = actor.image;
    img.loading = 'lazy';
    img.decoding = 'async';
    img.onerror = () => { img.style.visibility = 'hidden'; };
    const meta = document.createElement('div');
    meta.className = `${NS}-meta`;
    const name = document.createElement('div');
    name.className = `${NS}-name`;
    name.textContent = actor.name || actor.imdbId;
    const ch = document.createElement('div');
    ch.className = `${NS}-char`;
    ch.textContent = actor.character || '';
    meta.appendChild(name); meta.appendChild(ch);
    r.appendChild(img); r.appendChild(meta); r.appendChild(action);
    return r;
  }

  function getDisplayCast() {
    // The UI runs in the top frame, but X-Ray data was ingested inside the
    // `starlight-iframe`. We therefore rely on the shared localStorage cache,
    // refreshed on every ingest (via publishCast) or via BroadcastChannel.
    if (idToInfo.size > 0) {
      const out = [];
      for (const [imdbId, info] of idToInfo) {
        if (info && info.name) out.push({ imdbId, name: info.name, character: info.character || null, image: info.image || null });
      }
      return out;
    }
    try {
      const raw = localStorage.getItem(LS_CAST_KEY);
      if (!raw) return [];
      const obj = JSON.parse(raw);
      return Array.isArray(obj.cast) ? obj.cast : [];
    } catch { return []; }
  }

  function refreshUI() {
    if (!panelEl) return;
    const body = panelEl.querySelector(`#${NS}-body`);
    body.innerHTML = '';
    const blList = loadBlacklist();
    const blSet = new Set(blList.map(e => e.imdbId));
    const detectedCast = getDisplayCast();

    panelEl.querySelector(`#${NS}-stats`).textContent =
      `${segments.length} segments · ${detectedCast.length} actors detected · ${blList.length} blocked`;

    if (currentTab === 'blacklist') {
      // Search field on top to add from the detected cast
      const add = document.createElement('div');
      add.className = `${NS}-add`;
      add.innerHTML = `<input type="text" placeholder="Search the detected cast…">`;
      const inp = add.querySelector('input');
      inp.addEventListener('input', () => refreshUI._suggest(inp.value, suggestBox));
      body.appendChild(add);
      const suggestBox = document.createElement('div');
      body.appendChild(suggestBox);

      if (!blList.length) {
        const e = document.createElement('div');
        e.className = `${NS}-empty`;
        e.textContent = 'No blacklisted actor yet.';
        body.appendChild(e);
        return;
      }
      const castMap = new Map(detectedCast.map(c => [c.imdbId, c]));
      for (const a of blList) {
        const info = castMap.get(a.imdbId) || { name: a.name, character: null, image: null };
        const btn = document.createElement('button');
        btn.className = `${NS}-btn ${NS}-danger`;
        btn.textContent = '×';
        btn.title = 'Remove from blacklist';
        btn.addEventListener('click', () => {
          saveBlacklist(loadBlacklist().filter(x => x.imdbId !== a.imdbId));
          lastSkippedSegment = null;  // allow re-evaluation
        });
        body.appendChild(rowFor({ imdbId: a.imdbId, name: info.name || a.name, character: info.character, image: info.image }, btn));
      }
    } else {
      // Cast tab: every person seen in the current X-Ray payload.
      const all = detectedCast.slice().sort((a, b) => (a.name || '').localeCompare(b.name || ''));
      if (!all.length) {
        const e = document.createElement('div');
        e.className = `${NS}-empty`;
        e.textContent = 'No actor detected yet. Start playback (or open a title page) and re-open this panel.';
        body.appendChild(e);
        return;
      }
      // Build all rows in a fragment first (single DOM write).
      const frag = document.createDocumentFragment();
      for (const a of all) {
        const blocked = blSet.has(a.imdbId);
        const btn = document.createElement('button');
        const setBtn = (isBlocked) => {
          btn.className = `${NS}-btn ${isBlocked ? `${NS}-active` : ''}`;
          btn.textContent = isBlocked ? '✓ blocked' : '🚫 block';
        };
        setBtn(blocked);
        btn.addEventListener('click', () => {
          // In-place toggle: do NOT call refreshUI (which would rebuild
          // the whole list and re-fetch every actor image — the freeze).
          const list = loadBlacklist();
          const isBlocked = list.some(x => x.imdbId === a.imdbId);
          const next = isBlocked
            ? list.filter(x => x.imdbId !== a.imdbId)
            : list.concat([{ imdbId: a.imdbId, name: a.name }]);
          saveBlacklist(next, { refresh: false });
          if (isBlocked) blSet.delete(a.imdbId); else blSet.add(a.imdbId);
          setBtn(!isBlocked);
          lastSkippedSegment = null;
        });
        frag.appendChild(rowFor(a, btn));
      }
      body.appendChild(frag);
    }
  }
  refreshUI._suggest = function (q, container) {
    container.innerHTML = '';
    q = (q || '').trim().toLowerCase();
    if (!q) return;
    const blSet = new Set(loadBlacklist().map(e => e.imdbId));
    const matches = getDisplayCast()
      .filter(c => !blSet.has(c.imdbId) && c.name && c.name.toLowerCase().includes(q))
      .slice(0, 6);
    for (const c of matches) {
      const btn = document.createElement('button');
      btn.className = `${NS}-btn`;
      btn.textContent = '+ block';
      btn.addEventListener('click', () => {
        const list = loadBlacklist();
        list.push({ imdbId: c.imdbId, name: c.name });
        saveBlacklist(list);
      });
      container.appendChild(rowFor(c, btn));
    }
  };

  // ──────────────────────────────────────────────────────────────────────────
  //  Minimal toast
  // ──────────────────────────────────────────────────────────────────────────
  let toastEl = null, toastTimer = null;
  function showToast(msg) {
    if (!toastEl) {
      toastEl = document.createElement('div');
      toastEl.className = `${NS}-toast`;
      document.body.appendChild(toastEl);
    }
    toastEl.textContent = msg;
    toastEl.style.opacity = '1';
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => { toastEl.style.opacity = '0'; }, 1800);
  }

  // ──────────────────────────────────────────────────────────────────────────
  //  Boot: UI in top frame only, hooks + skip engine in every frame
  // ──────────────────────────────────────────────────────────────────────────
  function boot() {
    if (!document.body) { setTimeout(boot, 50); return; }

    // Skip engine: watch <video> elements in THIS document (parent or iframe).
    const mo = new MutationObserver(() => bindToVideo());
    mo.observe(document.documentElement, { childList: true, subtree: true });
    bindToVideo();

    // BroadcastChannel: 'reset' is handled in every frame; 'cast' only in top.
    if (bc) {
      bc.onmessage = (ev) => {
        if (!ev || !ev.data) return;
        if (ev.data.type === 'reset') {
          idToInfo = new Map();
          segments = [];
          lastSkippedSegment = null;
          if (IS_TOP) {
            try { localStorage.removeItem(LS_CAST_KEY); } catch (_) {}
            refreshUI();
          }
          return;
        }
        if (IS_TOP && ev.data.type === 'cast' && Array.isArray(ev.data.cast)) {
          // REPLACE (not append): each broadcast carries the full cast
          // for the current title.
          const next = new Map();
          for (const c of ev.data.cast) {
            next.set(c.imdbId, {
              name: c.name || null,
              character: c.character || null,
              image: c.image || null,
            });
          }
          idToInfo = next;
          refreshUI();
        }
      };
    }

    if (IS_TOP) {
      buildUI();
      // Also react to localStorage changes from other tabs.
      window.addEventListener('storage', (ev) => {
        if (ev.key === LS_KEY || ev.key === LS_CAST_KEY) refreshUI();
      });
      // SPA navigation: Prime Video swaps titles via history.pushState without
      // a full reload. Detect URL change and reset the in-memory + cached cast
      // so the panel never shows the previous title's actors.
      installNavWatcher();
    }
    LOG('Init OK (' + FRAME_TAG + ').');
  }

  function titleKeyFromUrl(href) {
    // Try to extract a stable title id from primevideo URLs:
    //   /detail/<ASIN>           ← series/movie page
    //   /play/<ASIN>             ← player URL
    //   ?gti=<ASIN> / ?asin=...  ← occasional query forms
    const m = href.match(/\/(?:detail|play)\/([A-Z0-9]{10,})/i)
            || href.match(/[?&](?:gti|asin)=([A-Z0-9]{10,})/i);
    return m ? m[1] : href.split('?')[0];  // fallback : path without query
  }

  function installNavWatcher() {
    let lastKey = titleKeyFromUrl(location.href);
    const onMaybeChange = () => {
      const k = titleKeyFromUrl(location.href);
      if (k === lastKey) return;
      lastKey = k;
      LOG('Title changed →', k, '· clearing cast/segments');
      idToInfo = new Map();
      segments = [];
      lastSkippedSegment = null;
      try { localStorage.removeItem(LS_CAST_KEY); } catch (_) {}
      if (bc) try { bc.postMessage({ type: 'reset' }); } catch (_) {}
      refreshUI();
    };
    // Patch pushState/replaceState (single-page navigation) + listen popstate.
    const wrap = (fn) => function () {
      const r = fn.apply(this, arguments);
      try { onMaybeChange(); } catch (_) {}
      return r;
    };
    try {
      history.pushState = wrap(history.pushState);
      history.replaceState = wrap(history.replaceState);
    } catch (_) {}
    window.addEventListener('popstate', onMaybeChange, { passive: true });
    // Cheap polling as a safety net (some routers don't go through pushState).
    setInterval(onMaybeChange, 1500);
  }
  boot();
})();
