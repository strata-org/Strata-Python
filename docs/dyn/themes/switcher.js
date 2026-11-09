// switcher.js — the "Style" menu. The pre-paint part (reading ?query and localStorage and
// setting <html data-*>) is in the inline preload script that DynIntroMain.lean puts in
// <head>; this file only builds the menu once the DOM exists.
// Verso puts extraJs before extraHead, so this runs before the preload script: defer
// everything to DOMContentLoaded, when window.__dynStyle exists.
function dynSwitcher() {
  var S = window.__dynStyle;
  if (!S) return;
  var OPTIONS = {
    theme: [['system', 'System'], ['light', 'Light'], ['dark', 'Dark'], ['hc', 'High contrast']],
    palette: [['a', 'A · Slate and sky'], ['b', 'B · Paper and ink'],
              ['c', 'C · Navy and violet'], ['d', 'D · Ink and blue']],
    font: [['default', 'Layout default'], ['system', 'System UI'], ['plex-sans', 'IBM Plex Sans'],
           ['system-serif', 'System serif']],
    code: [['default', 'Layout default'], ['system', 'System mono'], ['plex-mono', 'IBM Plex Mono']],
    size: [['s', 'S'], ['m', 'M'], ['l', 'L'], ['xl', 'XL']]
  };
  var LABELS = { theme: 'Theme', palette: 'Palette', font: 'Body font', code: 'Code font', size: 'Text size' };
  var html = document.documentElement;

  function current() {
    var o = {};
    S.keys.forEach(function (k) { o[k] = html.dataset[k]; });
    return o;
  }
  function save() {
    var cur = current(), out = {};
    // Store only what differs from the defaults, so new defaults still apply.
    S.keys.forEach(function (k) { if (cur[k] !== S.defaults[k]) out[k] = cur[k]; });
    try { localStorage.setItem(S.key, JSON.stringify(out)); } catch (e) {}
  }
  function shareUrl() {
    var cur = current(), q = [];
    S.keys.forEach(function (k) { if (cur[k] !== S.defaults[k]) q.push(k + '=' + encodeURIComponent(cur[k])); });
    var base = location.href.split('#')[0].split('?')[0];
    return base + (q.length ? '?' + q.join('&') : '') + location.hash;
  }
  function syncAddressBar() {
    try { history.replaceState(null, '', shareUrl()); } catch (e) {}
  }

  function build() {
    var root = document.createElement('div');
    root.className = 'style-switcher';
    var panelId = 'ss-panel';
    root.innerHTML =
      '<button type="button" class="ss-toggle" aria-expanded="false" aria-controls="' + panelId + '">' +
      '<span class="ss-aa" aria-hidden="true">Aa</span><span>Style</span></button>' +
      '<div class="ss-panel" id="' + panelId + '" role="dialog" aria-label="Style settings" hidden>' +
      '<h2>Style</h2></div>';
    var panel = root.querySelector('.ss-panel');
    ['theme', 'palette', 'font', 'code'].forEach(function (k) {
      var row = document.createElement('div');
      row.className = 'ss-row';
      var id = 'ss-' + k;
      var sel = '<select id="' + id + '" data-k="' + k + '">' + OPTIONS[k].map(function (o) {
        return '<option value="' + o[0] + '">' + o[1] + '</option>';
      }).join('') + '</select>';
      row.innerHTML = '<label for="' + id + '">' + LABELS[k] + '</label>' + sel;
      panel.appendChild(row);
    });
    var sizeRow = document.createElement('div');
    sizeRow.className = 'ss-row';
    sizeRow.innerHTML = '<label id="ss-size-l">Text size</label><div class="ss-seg" role="group" aria-labelledby="ss-size-l">' +
      OPTIONS.size.map(function (o) { return '<button type="button" data-size="' + o[0] + '">' + o[1] + '</button>'; }).join('') + '</div>';
    panel.appendChild(sizeRow);
    var actions = document.createElement('div');
    actions.innerHTML =
      '<div class="ss-actions"><button type="button" class="primary" data-a="copy">Copy link</button>' +
      '<button type="button" data-a="reset">Reset</button></div>' +
      '<input class="ss-link" readonly aria-label="Shareable link to this style">' +
      '<div class="ss-note">Saved in this browser. A link with <code>?palette=…&amp;theme=…</code> applies and saves it.</div>';
    panel.appendChild(actions);

    function refresh() {
      var cur = current();
      panel.querySelectorAll('select').forEach(function (s) { s.value = cur[s.dataset.k]; });
      panel.querySelectorAll('.ss-seg button').forEach(function (b) {
        b.setAttribute('aria-pressed', String(b.dataset.size === cur.size));
      });
      panel.querySelector('.ss-link').value = shareUrl();
    }
    function set(k, v) { html.dataset[k] = v; save(); syncAddressBar(); refresh(); }

    panel.addEventListener('change', function (ev) {
      var s = ev.target.closest('select');
      if (s) set(s.dataset.k, s.value);
    });
    panel.addEventListener('click', function (ev) {
      var b = ev.target.closest('button');
      if (!b) return;
      if (b.dataset.size) set('size', b.dataset.size);
      if (b.dataset.a === 'reset') {
        S.keys.forEach(function (k) { html.dataset[k] = S.defaults[k]; });
        save(); syncAddressBar(); refresh();
      }
      if (b.dataset.a === 'copy') {
        var url = shareUrl(), done = function () { b.textContent = 'Copied'; setTimeout(function () { b.textContent = 'Copy link'; }, 1200); };
        var input = panel.querySelector('.ss-link');
        input.value = url;
        if (navigator.clipboard && window.isSecureContext) navigator.clipboard.writeText(url).then(done, function () { input.select(); document.execCommand('copy'); done(); });
        else { input.select(); try { document.execCommand('copy'); } catch (e) {} done(); }
      }
    });
    var toggle = root.querySelector('.ss-toggle');
    function open(o) {
      panel.hidden = !o;
      toggle.setAttribute('aria-expanded', String(o));
      if (o) { refresh(); panel.querySelector('select').focus(); }
    }
    toggle.addEventListener('click', function () { open(panel.hidden); });
    document.addEventListener('keydown', function (ev) {
      if (ev.key === 'Escape' && !panel.hidden) { open(false); toggle.focus(); }
    });
    document.addEventListener('click', function (ev) {
      if (!panel.hidden && !root.contains(ev.target)) open(false);
    });
    refresh();

    // In the header when the layout shows one, otherwise floating top right.
    var header = document.querySelector('body > header');
    if (header && getComputedStyle(header).display !== 'none') header.appendChild(root);
    else { root.classList.add('floating'); document.body.appendChild(root); }
  }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', build);
  else build();
}
document.addEventListener('DOMContentLoaded', dynSwitcher);
