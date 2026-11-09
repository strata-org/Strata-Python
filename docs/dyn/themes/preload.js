// preload.js — runs synchronously in <head>, before first paint. DynIntroMain.lean
// substitutes the document's defaults for __DEFAULTS__. Precedence: ?query > localStorage > defaults.
(function () {
  var D = __DEFAULTS__;
  var ALLOWED = {
    palette: ['a', 'b', 'c', 'd'],
    theme: ['system', 'light', 'dark', 'hc'],
    font: ['default', 'system', 'plex-sans', 'system-serif'],
    code: ['default', 'system', 'plex-mono'],
    size: ['s', 'm', 'l', 'xl']
  };
  var keys = Object.keys(ALLOWED);
  var KEY = D.key;
  var s = {};
  try { s = JSON.parse(localStorage.getItem(KEY) || '{}') || {}; } catch (e) {}
  var q = new URLSearchParams(location.search), fromUrl = false;
  keys.forEach(function (k) { if (q.has(k)) { s[k] = q.get(k); fromUrl = true; } });
  var h = document.documentElement;
  keys.forEach(function (k) {
    var v = s[k];
    h.dataset[k] = ALLOWED[k].indexOf(v) >= 0 ? v : D[k];
  });
  if (fromUrl) {
    var out = {};
    keys.forEach(function (k) { if (h.dataset[k] !== D[k]) out[k] = h.dataset[k]; });
    try { localStorage.setItem(KEY, JSON.stringify(out)); } catch (e) {}
  }
  window.__dynStyle = { defaults: D, key: KEY, keys: keys };
})();
