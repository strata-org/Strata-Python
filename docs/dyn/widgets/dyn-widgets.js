// dyn-widgets.js: the six interactive panels of "Introduction to Dyn".
// Their data comes from intro-data.js (see data()), which scripts/export-data.py writes; the
// static listings are highlighted when the document is built.
"use strict";
(function () {
  // ---------------------------------------------------------------- utilities
  // Every artefact comes from intro-data.js, one asset shared by every page. A deep copy
  // keeps each widget's view independent.
  function data(id) {
    var all = window.DYN_INTRO_DATA;
    return all && all[id] ? JSON.parse(JSON.stringify(all[id])) : null;
  }
  function $(id) { return document.getElementById(id); }
  function esc(s) {
    return String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
  }
  function show(el) { if (el) el.hidden = false; }
  function reveal(root) {
    var els = root.querySelectorAll(".js-only");
    for (var i = 0; i < els.length; i++) els[i].hidden = false;
    var nj = root.querySelectorAll(".nojs-note");
    for (var j = 0; j < nj.length; j++) nj[j].hidden = true;
  }
  function fail(root, msg) {
    var p = document.createElement("p");
    p.className = "status bad";
    p.textContent = "This panel could not start: " + msg + ". The static text above is unaffected.";
    root.appendChild(p);
  }

  // ---------------------------------------------------------------- highlighting
  var RULES = {
    dyn: [
      ["t-com", /^--.*$/],
      ["t-kw", /^(?:module|func|jump|branch|ret|unreachable|const)\b/],
      ["t-val", /^%[A-Za-z_][\w.]*/],
      ["t-fn", /^@[A-Za-z_][\w.]*/],
      ["t-label", /^\^[A-Za-z_][\w.]*/],
      ["t-op", /^(?:base|while|py)\.[A-Za-z_][\w.]*(?=[\[(]|\s|$)/],
      ["t-num", /^-?\d+/]
    ],
    lean: [
      ["t-com", /^(?:--.*$|\/-[\s\S]*?-\/|\/\*[\s\S]*?\*\/)/],
      ["t-str", /^"(?:[^"\\]|\\.)*"/],
      ["t-kw", /^(?:public|private|environment|extends|where|namespace|open|end|data|type|insn|terminal|abbrev|mutual|def|let|do|if|then|else|match|with|return|fun|for|in|unless|mut|structure|instance|inductive|deriving|section|variable|theorem|op|category|dialect)\b/],
      ["t-fn", /^(?:@\[[^\]]*\]|#[a-z_]+)/],
      ["t-type", /^(?:Int|Bool|Unit|Nat|Array|List|Sem|Label|Region|Flow|IntList|Cell|Value|Except|Ref|Fn|Code|Exp|Stmt|Body|Ident)\b/],
      ["t-num", /^\d+/]
    ],
    while: [
      ["t-kw", /^(?:fun|var|while|try|catch|return|print|raise|region|if|else|ref|case|of|wcell)\b/],
      ["t-type", /^(?:Int|Bool|Unit|IntList|Ref|ListRef|Cell)\b/],
      ["t-num", /^\d+/]
    ]
  };
  function highlight(lang, text) {
    var rules = RULES[lang];
    if (!rules) return esc(text);
    var out = "", i = 0, plain = "";
    while (i < text.length) {
      var rest = text.slice(i), hit = null;
      var prev = i > 0 ? text[i - 1] : " ";
      if (/[\w.%@^]/.test(prev) && !/^(?:--|\/-|\/\*|")/.test(rest)) { plain += text[i]; i++; continue; }
      for (var r = 0; r < rules.length; r++) {
        var m = rules[r][1].exec(rest);
        if (m && m[0].length) { hit = [rules[r][0], m[0]]; break; }
      }
      if (hit) {
        out += esc(plain); plain = "";
        out += '<span class="' + hit[0] + '">' + esc(hit[1]) + "</span>";
        i += hit[1].length;
      } else { plain += text[i]; i++; }
    }
    return out + esc(plain);
  }
  function linesInto(pre, lang, text) {
    var lines = text.split("\n");
    pre.innerHTML = lines.map(function (l, i) {
      return '<span class="ln" data-line="' + i + '">' + (highlight(lang, l) || " ") + "</span>";
    }).join("");
    return pre.querySelectorAll(".ln");
  }

  // ---------------------------------------------------------------- Dyn parser
  function splitTop(s) {
    var out = [], depth = 0, cur = "";
    for (var i = 0; i < s.length; i++) {
      var c = s[i];
      if (c === "(" || c === "[") depth++;
      if (c === ")" || c === "]") depth--;
      if (c === "," && depth === 0) { out.push(cur.trim()); cur = ""; } else cur += c;
    }
    if (cur.trim()) out.push(cur.trim());
    return out;
  }
  function closing(s, i) {
    var open = s[i], close = open === "(" ? ")" : "]", depth = 0;
    for (var j = i; j < s.length; j++) {
      if (s[j] === "(" || s[j] === "[") depth++;
      if (s[j] === ")" || s[j] === "]") { depth--; if (depth === 0) { if (s[j] !== close) throw new Error("unbalanced"); return j; } }
    }
    throw new Error("unbalanced brackets in: " + s);
  }
  function parseOperand(t) {
    if (t[0] === "%") return { v: t.slice(1) };
    if (t[0] === "@") return { fn: t.slice(1) };
    if (/^-?\d+$/.test(t)) return { lit: { t: "int", v: BigInt(t) } };
    if (t === "true" || t === "false") return { lit: { t: "bool", v: t === "true" } };
    if (t === "unit") return { lit: { t: "unit" } };
    return { unknown: t };
  }
  function parseApp(s) {
    var i = 0;
    while (i < s.length && "[( ".indexOf(s[i]) < 0) i++;
    var app = { op: s.slice(0, i), targs: null, args: [], succs: [], opensRegion: false };
    if (s[i] === "[") { var j = closing(s, i); app.targs = s.slice(i + 1, j); i = j + 1; }
    if (s[i] === "(") { var k = closing(s, i); app.args = splitTop(s.slice(i + 1, k)).map(parseOperand); i = k + 1; }
    for (;;) {
      var rest = s.slice(i);
      var m = /^ \^([\w.]+)\(/.exec(rest);
      if (!m) break;
      var start = i + m[0].length - 1, end = closing(s, start);
      app.succs.push({ target: m[1], args: splitTop(s.slice(start + 1, end)).map(parseOperand) });
      i = end + 1;
    }
    var tail = s.slice(i).trim();
    if (tail === "{") app.opensRegion = true;
    else if (tail) throw new Error("cannot read: " + s);
    return app;
  }
  function parseDecls(s) {
    return splitTop(s).map(function (d) {
      var m = /^%(\S+) : (.+)$/.exec(d);
      if (!m) throw new Error("bad parameter " + d);
      return { name: m[1], type: m[2] };
    });
  }
  var HEADER = /^([\w.]+)\((.*)\):$/;
  function newBody(owner, parent) { return { blocks: [], owner: owner, parent: parent, regions: [] }; }
  function parseDyn(text) {
    var lines = text.split("\n"), mod = { funcs: [] }, fn = null, body = null, block = null, stack = [];
    lines.forEach(function (raw, idx) {
      var line = raw.trim(), m;
      if (!line || /^module /.test(line)) return;
      if ((m = /^func @(\S+)\((.*)\) -> (.*) \{$/.exec(line))) {
        fn = { name: m[1], params: m[2] ? parseDecls(m[2]) : [], ret: m[3], start: idx, end: idx };
        body = fn.body = newBody(null, null); body.fn = fn; block = null; mod.funcs.push(fn); return;
      }
      if (line === "}" || line === "} {") {
        if (stack.length) {
          var owner = body.owner;
          var fr = stack.pop(); body = fr.body; block = fr.block;
          if (line === "} {") {
            stack.push({ body: body, block: block });
            var nb = newBody(owner, body); nb.fn = fn; owner.regions.push(nb); body.regions.push(nb);
            body = nb; block = null;
          }
        } else if (fn) { fn.end = idx; fn = null; }
        return;
      }
      if (!fn) return;
      if ((m = HEADER.exec(line))) {
        block = { label: m[1], params: m[2] ? parseDecls(m[2]) : [],
                  instrs: [], term: null, line: idx, body: body };
        body.blocks.push(block); return;
      }
      if (!block) throw new Error("line outside a block: " + line);
      var ins, a = null;
      if ((m = /^%(\S+) : (.+?) = (.*)$/.exec(line))) {
        var rhs = m[3];
        if (/^const /.test(rhs)) ins = { result: m[1], type: m[2], op: "const", args: [parseOperand(rhs.slice(6))], succs: [], line: idx };
        else { a = parseApp(rhs); ins = { result: m[1], type: m[2], op: a.op, targs: a.targs, args: a.args, succs: a.succs, line: idx, regions: [] }; }
        ins.index = block.instrs.length; ins.block = block;
        block.instrs.push(ins);
        if (a && a.opensRegion) open(ins);
      } else {
        var t = parseApp(line);
        block.term = { op: t.op, args: t.args, succs: t.succs, line: idx, block: block, regions: [] };
        if (t.opensRegion) open(block.term);
      }
      function open(owner) {
        owner.regions = owner.regions || [];
        stack.push({ body: body, block: block });
        var rb = newBody(owner, body); rb.fn = fn; owner.regions.push(rb); body.regions.push(rb);
        body = rb; block = null;
      }
    });
    return mod;
  }
  function blockByLabel(body, l) {
    for (var i = 0; i < body.blocks.length; i++) if (body.blocks[i].label === l) return body.blocks[i];
    return null;
  }
  // Points: {label, k}.  Parent of <l,k+1> is <l,k>; of <l,0>, idom(l).
  function edgesOf(body) {
    var es = [];
    body.blocks.forEach(function (b) {
      b.instrs.forEach(function (ins, j) {
        ins.succs.forEach(function (s) { es.push({ from: b.label, k: j, to: s.target, err: true, line: ins.line, via: ins.result }); });
      });
      if (b.term) b.term.succs.forEach(function (s) { es.push({ from: b.label, k: b.instrs.length, to: s.target, err: false, line: b.term.line }); });
    });
    return es;
  }
  function makeParent(idom) {
    return function (p) {
      if (p.k > 0) return { label: p.label, k: p.k - 1 };
      var d = idom[p.label];
      return d ? { label: d.label, k: d.count } : null;
    };
  }
  function isAnc(parent, a, p) {
    for (var q = p; q; q = parent(q)) if (q.label === a.label && q.k === a.k) return true;
    return false;
  }
  // The printed form stores no tree, so the tree is computed from the graph, once per body.
  function idomsOf(body) {
    if (!body.idoms) body.idoms = computeIdoms(body);
    return body.idoms;
  }
  // Cooper, Harvey and Kennedy over points.
  function computeIdoms(body) {
    var es = edgesOf(body), entry = body.blocks[0].label;
    var preds = {}; body.blocks.forEach(function (b) { preds[b.label] = []; });
    es.forEach(function (e) { if (preds[e.to]) preds[e.to].push(e); });
    var order = [], seen = {};
    (function dfs(l) {
      if (seen[l]) return; seen[l] = true;
      es.filter(function (e) { return e.from === l; }).forEach(function (e) { if (preds[e.to]) dfs(e.to); });
      order.push(l);
    })(entry);
    order.reverse();
    var idom = {}; idom[entry] = null;
    var done = {}; done[entry] = true;
    var parent = makeParent(idom);
    function inter(p, q) {
      var anc = {};
      for (var x = p; x; x = parent(x)) anc[x.label + ":" + x.k] = true;
      for (var y = q; y; y = parent(y)) if (anc[y.label + ":" + y.k]) return y;
      return null;
    }
    var changed = true, rounds = 0;
    while (changed && rounds++ < 100) {
      changed = false;
      order.forEach(function (l) {
        if (l === entry) return;
        var cur = null;
        preds[l].forEach(function (e) {
          if (!done[e.from]) return;
          var p = { label: e.from, k: e.k };
          cur = cur ? inter(cur, p) : p;
        });
        if (!cur) return;
        var old = idom[l];
        if (!old || old.label !== cur.label || old.count !== cur.k) {
          idom[l] = { label: cur.label, count: cur.k }; done[l] = true; changed = true;
        }
      });
    }
    return idom;
  }
  // Definitions and uses of one function, by body, for the value highlighter.
  function defsUses(fn) {
    var defs = {}, uses = [];
    function walk(body) {
      body.blocks.forEach(function (b, bi) {
        b.params.forEach(function (p) { defs[p.name] = { body: body, pt: { label: b.label, k: 0 }, line: b.line }; });
        b.instrs.forEach(function (ins, j) {
          defs[ins.result] = { body: body, pt: { label: b.label, k: j + 1 }, line: ins.line };
          var vs = ins.args.concat([].concat.apply([], ins.succs.map(function (s) { return s.args; })));
          vs.forEach(function (o) { if (o.v) uses.push({ name: o.v, body: body, pt: { label: b.label, k: j }, line: ins.line }); });
          (ins.regions || []).forEach(walk);
        });
        if (b.term) {
          var tv = b.term.args.concat([].concat.apply([], b.term.succs.map(function (s) { return s.args; })));
          tv.forEach(function (o) { if (o.v) uses.push({ name: o.v, body: body, pt: { label: b.label, k: b.instrs.length }, line: b.term.line }); });
          (b.term.regions || []).forEach(walk);
        }
      });
    }
    walk(fn.body);
    return { defs: defs, uses: uses };
  }
  function ownerPoint(body) {
    var o = body.owner;
    if (o.index !== undefined) return { label: o.block.label, k: o.index };
    return { label: o.block.label, k: o.block.instrs.length };
  }
  function inScope(def, use) {
    var body = use.body, pt = use.pt;
    for (;;) {
      if (def.body === body) return isAnc(makeParent(idomsOf(body)), def.pt, pt);
      if (!body.owner) return false;
      pt = ownerPoint(body); body = body.parent;
    }
  }

  // ---------------------------------------------------------------- A: stepper
  function initStepper() {
    var root = $("w-stepper"), d = data("doc-source");
    var srcPre = $("stp-src"), mPre = $("stp-dyn");
    var mlines = d.dynFolded.split("\n");
    var errs = [];
    d.steps.forEach(function (s, si) {
      s.lines.forEach(function (ln, k) {
        if (!new RegExp(s.match[k]).test(mlines[ln] || "")) errs.push("step " + (si + 1) + " line " + ln);
      });
    });
    var lineEls = linesInto(mPre, "dyn", d.dynFolded);
    // source segments
    var cuts = {}; cuts[0] = true; cuts[d.source.length] = true;
    d.steps.forEach(function (s) { cuts[s.srcStart] = true; cuts[s.srcEnd] = true; });
    var pts = Object.keys(cuts).map(Number).sort(function (a, b) { return a - b; });
    var html = "";
    for (var i = 0; i + 1 < pts.length; i++) {
      var a = pts[i], b = pts[i + 1];
      var cover = [];
      d.steps.forEach(function (s, si) { if (s.srcStart <= a && b <= s.srcEnd) cover.push(si); });
      html += '<span class="seg" data-a="' + a + '" data-steps="' + cover.join(",") + '">' + highlight("while", d.source.slice(a, b)) + "</span>";
    }
    srcPre.innerHTML = html;
    var segs = srcPre.querySelectorAll(".seg");
    var cur = 0;
    function paint(si) {
      var s = d.steps[si];
      for (var i = 0; i < segs.length; i++) {
        var a = +segs[i].getAttribute("data-a");
        segs[i].classList.toggle("hl", a >= s.srcStart && a < s.srcEnd);
      }
      for (var j = 0; j < lineEls.length; j++) lineEls[j].classList.toggle("hl", s.lines.indexOf(j) >= 0);
    }
    function set(si) {
      cur = si; paint(si);
      $("stp-caption").textContent = d.steps[si].caption;
      $("stp-count").textContent = "Step " + (si + 1) + " of " + d.steps.length;
      $("stp-prev").disabled = si === 0; $("stp-next").disabled = si === d.steps.length - 1;
    }
    function smallest(list) {
      var best = -1;
      list.forEach(function (si) {
        if (best < 0 || (d.steps[si].srcEnd - d.steps[si].srcStart) < (d.steps[best].srcEnd - d.steps[best].srcStart)) best = si;
      });
      return best;
    }
    srcPre.addEventListener("mouseover", function (ev) {
      var seg = ev.target.closest(".seg"); if (!seg) return;
      var list = seg.getAttribute("data-steps"); if (!list) return;
      var si = smallest(list.split(",").map(Number)); if (si >= 0) paint(si);
    });
    mPre.addEventListener("mouseover", function (ev) {
      var ln = ev.target.closest(".ln"); if (!ln) return;
      var n = +ln.getAttribute("data-line"), list = [];
      d.steps.forEach(function (s, si) { if (s.lines.indexOf(n) >= 0) list.push(si); });
      var si = smallest(list); if (si >= 0) paint(si);
    });
    srcPre.addEventListener("mouseleave", function () { paint(cur); });
    mPre.addEventListener("mouseleave", function () { paint(cur); });
    $("stp-prev").addEventListener("click", function () { if (cur > 0) set(cur - 1); });
    $("stp-next").addEventListener("click", function () { if (cur < d.steps.length - 1) set(cur + 1); });
    reveal(root);
    if (errs.length) { var e = $("stp-err"); e.hidden = false; e.textContent = "Golden check: step line patterns do not match the print at " + errs.join("; ") + "."; }
    else $("stp-err").hidden = true;
    set(0);
  }

  // ---------------------------------------------------------------- B: fold toggle
  function funcSlice(text, name) {
    var ls = text.split("\n"), out = [], on = false;
    for (var i = 0; i < ls.length; i++) {
      if (/^\s*func @/.test(ls[i])) on = ls[i].indexOf("func @" + name + "(") >= 0;
      if (on) { out.push(ls[i]); if (/^  \}$/.test(ls[i])) on = false; }
    }
    return out.join("\n");
  }
  function initFold() {
    var root = $("w-fold"), d = data("doc-full"), pre = $("fold-text");
    var full = false;
    function render() {
      var name = $("fold-fn").value;
      var a = funcSlice(d.dynFolded, name), b = funcSlice(d.dynFull, name);
      var mine = full ? b : a, other = full ? a : b;
      var otherSet = {}; other.split("\n").forEach(function (l) { otherSet[l] = true; });
      var els = linesInto(pre, "dyn", mine);
      mine.split("\n").forEach(function (l, i) {
        if (/ = const /.test(l)) els[i].classList.add("ins");
        else if (!otherSet[l]) els[i].classList.add("chg");
      });
      $("fold-a").setAttribute("aria-checked", String(!full));
      $("fold-b").setAttribute("aria-checked", String(full));
      $("fold-a").tabIndex = full ? -1 : 0; $("fold-b").tabIndex = full ? 0 : -1;
    }
    $("fold-a").addEventListener("click", function () { full = false; render(); });
    $("fold-b").addEventListener("click", function () { full = true; render(); });
    [$("fold-a"), $("fold-b")].forEach(function (btn) {
      btn.addEventListener("keydown", function (ev) {
        if (["ArrowLeft", "ArrowRight", "ArrowUp", "ArrowDown"].indexOf(ev.key) >= 0) {
          ev.preventDefault(); full = !full; render(); (full ? $("fold-b") : $("fold-a")).focus();
        }
      });
    });
    $("fold-fn").addEventListener("change", render);
    reveal(root);
    render();
  }

  // ---------------------------------------------------------------- C: CFG
  var SVGNS = "http://www.w3.org/2000/svg";
  function svgEl(name, attrs, text) {
    var e = document.createElementNS(SVGNS, name);
    for (var k in attrs) e.setAttribute(k, attrs[k]);
    if (text !== undefined) e.textContent = text;
    return e;
  }
  function drawBody(body, title) {
    var es = edgesOf(body), blocks = body.blocks;
    var idx = {}; blocks.forEach(function (b, i) { idx[b.label] = i; });
    // layers: longest forward path (forward = to a later block in print order)
    var layer = {}; blocks.forEach(function (b) { layer[b.label] = 0; });
    blocks.forEach(function (b) {
      es.forEach(function (e) {
        if (e.from === b.label && idx[e.to] > idx[e.from]) layer[e.to] = Math.max(layer[e.to], layer[b.label] + 1);
      });
    });
    var rows = {}; blocks.forEach(function (b) { (rows[layer[b.label]] = rows[layer[b.label]] || []).push(b); });
    var W = 168, H = 42, GX = 40, GY = 46, PADX = 40, PADY = 16;
    var pos = {}, maxCols = 1, nrows = 0;
    Object.keys(rows).forEach(function (r) {
      maxCols = Math.max(maxCols, rows[r].length); nrows = Math.max(nrows, +r + 1);
    });
    var width = PADX * 2 + maxCols * W + (maxCols - 1) * GX + 60;
    Object.keys(rows).forEach(function (r) {
      var row = rows[r], rowW = row.length * W + (row.length - 1) * GX;
      var x0 = (width - rowW) / 2;
      row.forEach(function (b, i) { pos[b.label] = { x: x0 + i * (W + GX), y: PADY + (+r) * (H + GY) }; });
    });
    var height = PADY * 2 + nrows * H + (nrows - 1) * GY;
    var summary = title + ": " + blocks.length + " blocks; edges " + es.map(function (e) {
      return e.from + " to " + e.to + (e.err ? " (raising, from %" + e.via + ")" : "");
    }).join(", ") + ".";
    var svg = svgEl("svg", { width: width, height: height, viewBox: "0 0 " + width + " " + height, role: "img", "aria-label": summary });
    var defs = svgEl("defs", {});
    var mk = svgEl("marker", { id: "arr-" + title.replace(/\W/g, ""), viewBox: "0 0 10 10", refX: "9", refY: "5", markerWidth: "7", markerHeight: "7", orient: "auto-start-reverse" });
    mk.appendChild(svgEl("path", { d: "M0,0 L10,5 L0,10 z" }));
    defs.appendChild(mk); svg.appendChild(defs);
    var mid = "url(#" + mk.getAttribute("id") + ")";
    es.forEach(function (e, n) {
      var a = pos[e.from], b = pos[e.to]; if (!a || !b) return;
      var back = idx[e.to] <= idx[e.from];
      var path, lx, ly;
      if (back) {
        var x1 = a.x, y1 = a.y + H / 2, x2 = b.x, y2 = b.y + H / 2, bend = Math.min(a.x, b.x) - 30;
        path = "M" + x1 + "," + y1 + " C" + bend + "," + y1 + " " + bend + "," + y2 + " " + x2 + "," + y2;
      } else {
        var sx = a.x + W / 2 + (e.err ? 30 : 0), sy = a.y + H, tx = b.x + W / 2, ty = b.y;
        path = "M" + sx + "," + sy + " C" + sx + "," + (sy + GY / 2) + " " + tx + "," + (ty - GY / 2) + " " + tx + "," + ty;
        lx = (sx + tx) / 2 + 12; ly = (sy + ty) / 2 - 4;
      }
      var p = svgEl("path", { d: path, "class": "edge" + (e.err ? " err" : "") + (back ? " back" : ""), "marker-end": mid });
      p.appendChild(svgEl("title", {}, e.from + " → " + e.to + (e.err ? " (^err of %" + e.via + ")" : "")));
      svg.appendChild(p);
      if (e.err && lx !== undefined) svg.appendChild(svgEl("text", { x: lx, y: ly, "class": "elabel" }, "%" + e.via));
    });
    blocks.forEach(function (b, i) {
      var g = svgEl("g", { "class": "blk" }), q = pos[b.label];
      g.appendChild(svgEl("rect", { x: q.x, y: q.y, width: W, height: H, rx: 5 }));
      g.appendChild(svgEl("text", { x: q.x + 8, y: q.y + 17 }, b.label + (i === 0 ? "  (entry)" : "")));
      g.appendChild(svgEl("text", { x: q.x + 8, y: q.y + 33, "class": "sub" },
        b.params.length + " param" + (b.params.length === 1 ? "" : "s") + ", " + b.instrs.length + " line" + (b.instrs.length === 1 ? "" : "s")));
      g.appendChild(svgEl("title", {}, b.label + "(" + b.params.map(function (p) { return "%" + p.name; }).join(", ") + ")"));
      svg.appendChild(g);
    });
    return svg;
  }
  function treeHtml(body, idom) {
    var kids = {};
    body.blocks.forEach(function (b, i) {
      if (i === 0) return;
      var d = idom[b.label]; if (!d) return;
      (kids[d.label] = kids[d.label] || []).push({ b: b, at: d.count });
    });
    function node(label, parentLabel, at) {
      var s = "<li><code>" + esc(label) + "</code>" + (parentLabel === null ? " (entry)" : ' <span class="t-type">below ' + esc(parentLabel) + "[" + at + "]</span>");
      var ks = kids[label] || [];
      if (ks.length) s += "<ul>" + ks.map(function (k) { return node(k.b.label, label, k.at); }).join("") + "</ul>";
      return s + "</li>";
    }
    return "<ul>" + node(body.blocks[0].label, null, null) + "</ul>";
  }
  function initCfg() {
    var root = $("w-cfg");
    var texts = data("doc-cfg");
    var sel = $("cfg-sel");
    texts.forEach(function (t, i) { var o = document.createElement("option"); o.value = i; o.textContent = t.title; sel.appendChild(o); });
    var parsed = texts.map(function (t) { return parseDyn(t.text); });
    function allBodies(body, acc) { acc.push(body); body.regions.forEach(function (r) { allBodies(r, acc); }); return acc; }
    function render() {
      var i = +sel.value, t = texts[i], fn = parsed[i].funcs.filter(function (f) { return f.name === t.fn; })[0];
      var st = $("cfg-status"); st.hidden = true; st.className = "status";
      var svgBox = $("cfg-svg"); svgBox.innerHTML = ""; svgBox.appendChild(drawBody(fn.body, t.title));
      $("cfg-tree").innerHTML = treeHtml(fn.body, idomsOf(fn.body));
      var rbox = $("cfg-regions"); rbox.innerHTML = "";
      allBodies(fn.body, []).slice(1).forEach(function (rb, n) {
        var div = document.createElement("div"); div.className = "regionbox";
        var own = rb.owner.result ? "%" + rb.owner.result + " = " + rb.owner.op : rb.owner.op;
        div.innerHTML = '<div class="note">Region ' + (n + 1) + " of " + esc(own) + ": its own body, entered with everything in scope at the owning instruction visible.</div>";
        div.appendChild(drawBody(rb, t.title + " region " + (n + 1)));
        var tr = document.createElement("div"); tr.className = "domtree"; tr.innerHTML = treeHtml(rb, idomsOf(rb));
        div.appendChild(tr); rbox.appendChild(div);
      });
      // text with clickable values
      var lines = t.text.split("\n").slice(fn.start, fn.end + 1);
      var pre = $("cfg-text");
      pre.innerHTML = lines.map(function (l, k) {
        var h = highlight("dyn", l).replace(/<span class="t-val">%([\w.]+)<\/span>/g, function (_, n) {
          return '<span class="t-val v" tabindex="0" role="button" aria-label="value %' + n + '" data-v="' + n + '">%' + n + "</span>";
        });
        return '<span class="ln" data-line="' + (fn.start + k) + '">' + (h || " ") + "</span>";
      }).join("");
      var du = defsUses(fn);
      var bad = du.uses.filter(function (u) { var d = du.defs[u.name]; return !d || !inScope(d, u); });
      function pick(name) {
        var vs = pre.querySelectorAll(".v");
        var def = du.defs[name];
        for (var q = 0; q < vs.length; q++) {
          var el = vs[q], lnEl = el.closest(".ln"), ln = +lnEl.getAttribute("data-line");
          el.classList.remove("def", "use", "bad");
          if (el.getAttribute("data-v") !== name) continue;
          var text = lnEl.textContent.trim();
          var isHeader = HEADER.test(text);
          var first = lnEl.querySelector(".v") === el && new RegExp("^%" + name.replace(/\./g, "\\.") + " : ").test(text);
          var isDef = isHeader || first;
          el.classList.add(isDef ? "def" : "use");
          if (!isDef && bad.some(function (u) { return u.name === name && u.line === ln; })) el.classList.add("bad");
        }
        var n = du.uses.filter(function (u) { return u.name === name; }).length;
        st.hidden = false; st.className = "status ok";
        st.textContent = "%" + name + ": defined on line " + (def ? def.line - fn.start + 1 : "?") + " of this function (green), used " + n + " time" + (n === 1 ? "" : "s") + " (yellow); the definition dominates every use.";
        if (bad.some(function (u) { return u.name === name; })) { st.className = "status bad"; st.textContent = "%" + name + " has a use its definition does not dominate (red)."; }
      }
      pre.onclick = function (ev) { var v = ev.target.closest(".v"); if (v) pick(v.getAttribute("data-v")); };
      pre.onkeydown = function (ev) { if ((ev.key === "Enter" || ev.key === " ") && ev.target.classList.contains("v")) { ev.preventDefault(); pick(ev.target.getAttribute("data-v")); } };
      if (bad.length) { st.hidden = false; st.className = "status bad"; st.textContent = bad.length + " use(s) not dominated by their definitions."; }
    }
    sel.addEventListener("change", render);
    reveal(root);
    render();
  }

  // ---------------------------------------------------------------- D: interpreter
  function NotModelled(msg) { this.message = msg; }
  function ediv(a, b) { var q = a / b, r = a % b; if (r < 0n) q = b > 0n ? q - 1n : q + 1n; return q; }
  function emod(a, b) { var r = a % b; if (r < 0n) r += (b < 0n ? -b : b); return r; }
  function showVal(v) {
    if (!v) return "?";
    if (v.t === "int") return v.v.toString();
    if (v.t === "bool") return String(v.v);
    if (v.t === "unit") return "unit";
    if (v.t === "fn") return "@" + v.name;
    if (v.t === "ctor") return v.name + (v.fields.length ? "(" + v.fields.map(showVal).join(", ") + ")" : "");
    return "?";
  }
  function makeMachine(mod, entry, args) {
    var fns = {}; mod.funcs.forEach(function (f) { fns[f.name] = f; });
    var m = { frames: [], out: [], steps: 0, result: null, fault: null };
    function enter(fname, vals) {
      var f = fns[fname]; if (!f) throw new NotModelled("no function " + fname);
      var b = f.body.blocks[0], env = {};
      if (vals.length !== b.params.length) throw new NotModelled(fname + " takes " + b.params.length + " arguments");
      b.params.forEach(function (p, i) { env[p.name] = vals[i]; });
      m.frames.push({ fn: f, block: b, pc: 0, env: env, pending: null });
    }
    enter(entry, args.map(function (n) { return { t: "int", v: BigInt(n) }; }));
    function ev(fr, o) {
      if (o.v !== undefined) { if (!(o.v in fr.env)) throw new NotModelled("unbound %" + o.v); return fr.env[o.v]; }
      if (o.lit) return o.lit;
      if (o.fn) return { t: "fn", name: o.fn };
      throw new NotModelled("operand " + o.unknown);
    }
    function transfer(fr, succ, payload) {
      var tb = blockByLabel(fr.fn.body, succ.target);
      if (!tb) throw new NotModelled("no block " + succ.target);
      var vals = succ.args.map(function (o) { return ev(fr, o); }).concat(payload);
      if (vals.length !== tb.params.length) throw new NotModelled("edge to " + tb.label + " passes " + vals.length + " values");
      tb.params.forEach(function (p, i) { fr.env[p.name] = vals[i]; });
      fr.block = tb; fr.pc = 0;
    }
    function int2(vs) { vs.forEach(function (v) { if (v.t !== "int") throw new NotModelled("expected an integer"); }); return vs; }
    m.current = function () {
      var fr = m.frames[m.frames.length - 1]; if (!fr) return null;
      return fr.pc < fr.block.instrs.length ? fr.block.instrs[fr.pc].line : fr.block.term.line;
    };
    m.step = function () {
      if (m.result || m.fault) return false;
      var fr = m.frames[m.frames.length - 1];
      m.steps++;
      if (fr.pc < fr.block.instrs.length) {
        var ins = fr.block.instrs[fr.pc];
        if (ins.regions && ins.regions.length) throw new NotModelled(ins.op + " (regions)");
        var vs = ins.args.map(function (o) { return ev(fr, o); }), r;
        switch (ins.op) {
          case "const": r = vs[0]; break;
          case "while.add": int2(vs); r = { t: "int", v: vs[0].v + vs[1].v }; break;
          case "while.sub": int2(vs); r = { t: "int", v: vs[0].v - vs[1].v }; break;
          case "while.mul": int2(vs); r = { t: "int", v: vs[0].v * vs[1].v }; break;
          case "while.le": int2(vs); r = { t: "bool", v: vs[0].v <= vs[1].v }; break;
          case "while.lt": int2(vs); r = { t: "bool", v: vs[0].v < vs[1].v }; break;
          case "while.eq": int2(vs); r = { t: "bool", v: vs[0].v === vs[1].v }; break;
          case "while.ne": int2(vs); r = { t: "bool", v: vs[0].v !== vs[1].v }; break;
          case "while.div": case "while.mod":
            int2(vs);
            if (vs[1].v === 0n) { transfer(fr, ins.succs[0], [{ t: "int", v: 1n }]); return true; }
            r = { t: "int", v: ins.op === "while.div" ? ediv(vs[0].v, vs[1].v) : emod(vs[0].v, vs[1].v) }; break;
          case "while.print": int2(vs); m.out.push(vs[0].v); r = { t: "unit" }; break;
          case "base.ok": r = { t: "ctor", name: "ok", fields: vs }; break;
          case "base.error": r = { t: "ctor", name: "error", fields: vs }; break;
          case "base.callCode":
            if (vs[0].t !== "fn") throw new NotModelled("callCode on a non-function");
            fr.pending = ins.result; enter(vs[0].name, vs.slice(1)); return true;
          default: throw new NotModelled(ins.op);
        }
        fr.env[ins.result] = r; fr.pc++;
        return true;
      }
      var t = fr.block.term, tv = t.args.map(function (o) { return ev(fr, o); });
      switch (t.op) {
        case "jump": transfer(fr, t.succs[0], []); break;
        case "branch": transfer(fr, tv[0].v ? t.succs[0] : t.succs[1], []); break;
        case "ret":
          m.frames.pop();
          if (!m.frames.length) { m.result = tv[0]; return false; }
          var caller = m.frames[m.frames.length - 1];
          caller.env[caller.pending] = tv[0]; caller.pending = null; caller.pc++; break;
        case "base.Except.case":
          var c = tv[0]; if (c.t !== "ctor") throw new NotModelled("case on a non-constructor");
          transfer(fr, t.succs[c.name === "ok" ? 0 : 1], c.fields); break;
        case "unreachable": m.fault = "failure: unreachable"; return false;
        default: throw new NotModelled(t.op);
      }
      return true;
    };
    m.outcome = function () {
      if (m.fault) return "fault " + m.fault;
      var v = m.result; if (!v) return null;
      if (v.t === "ctor" && v.name === "ok") return "ok " + showVal(v.fields[0]);
      if (v.t === "ctor" && v.name === "error") return "raised " + showVal(v.fields[0]);
      return "ok " + showVal(v);
    };
    m.printed = function () { return "#[" + m.out.map(String).join(", ") + "]"; };
    return m;
  }
  function runToEnd(mod, entry, args, limit) {
    var m = makeMachine(mod, entry, args);
    while (m.step()) if (m.steps > limit) { m.fault = "out of fuel (this page)"; break; }
    return m;
  }
  function initInterp() {
    var root = $("w-interp"), d = data("doc-source"), outcomes = data("doc-outcomes");
    var mod = parseDyn(d.dynFolded);
    var banner = $("int-banner");
    var mism = [];
    outcomes.forEach(function (o) {
      try {
        var m = runToEnd(mod, o.entry, o.args, 100000);
        var got = m.outcome() + "; printed " + m.printed(), want = o.expected + "; printed " + o.printed;
        if (got !== want) mism.push(o.entry + " " + o.args.join(" ") + ": page " + got + ", expected " + want);
      } catch (e) { mism.push(o.entry + ": " + (e.message || e)); }
    });
    reveal(root);
    banner.hidden = false;
    if (mism.length) { banner.className = "status bad"; banner.textContent = "Outcome mismatch: " + mism.join("; "); }
    else {
      banner.className = "status ok";
      banner.textContent = "Outcomes match the expected outcomes (" + outcomes.map(function (o) {
        return o.entry + " " + o.args.join(" ") + ": " + o.expected;
      }).join("; ") + ").";
    }
    var srcPre = $("int-src");
    srcPre.innerHTML = highlight("while", d.source);
    var lineEls = linesInto($("int-dyn"), "dyn", d.dynFolded);
    var m = null;
    function srcSpanFor(line) {
      var best = null;
      d.steps.forEach(function (s) {
        if (s.lines.indexOf(line) >= 0 && (!best || s.srcEnd - s.srcStart < best.srcEnd - best.srcStart)) best = s;
      });
      return best;
    }
    function renderSrc(span) {
      if (!span) { srcPre.innerHTML = highlight("while", d.source); return; }
      srcPre.innerHTML = highlight("while", d.source.slice(0, span.srcStart)) + '<span class="seg hl">' +
        highlight("while", d.source.slice(span.srcStart, span.srcEnd)) + "</span>" + highlight("while", d.source.slice(span.srcEnd));
    }
    function render() {
      var cur = m ? m.current() : null;
      for (var i = 0; i < lineEls.length; i++) lineEls[i].classList.toggle("cur", i === cur);
      if (cur !== null && lineEls[cur] && lineEls[cur].scrollIntoView) {
        var pre = $("int-dyn"), el = lineEls[cur];
        if (el.offsetTop < pre.scrollTop || el.offsetTop > pre.scrollTop + pre.clientHeight - 20) pre.scrollTop = el.offsetTop - 40;
      }
      renderSrc(cur !== null ? srcSpanFor(cur) : null);
      $("int-steps").textContent = m ? "this page's steps (not the engine's count): " + m.steps : "";
      $("int-frames").innerHTML = m ? m.frames.slice().reverse().map(function (fr) {
        var bs = Object.keys(fr.env).map(function (k) { return "%" + esc(k) + " = " + esc(showVal(fr.env[k])); }).join(", ");
        return '<div class="frame"><b>' + esc(fr.fn.name) + "</b> in " + esc(fr.block.label) + ", line " + fr.pc + "<br>" + (bs || "(no values)") + "</div>";
      }).join("") || '<div class="frame">(no frames)</div>' : "";
      $("int-out").innerHTML = m ? '<div class="frame">' + esc(m.printed()) + "</div>" : "";
      var oc = m && m.outcome();
      $("int-result").innerHTML = oc ? '<div class="frame">' + esc(oc) + "</div>" : "";
      var over = !m || !!oc;
      $("int-step").disabled = over; $("int-run").disabled = over;
    }
    function reset() {
      var parts = $("int-args").value.trim().split(/\s+/);
      try {
        if (!parts[0] || parts.slice(1).some(function (p) { return !/^-?\d+$/.test(p); })) throw new NotModelled("write a function name and integers");
        m = makeMachine(mod, parts[0], parts.slice(1));
      } catch (e) {
        m = null; render();
        $("int-result").innerHTML = '<div class="frame">' + esc(e.message || String(e)) + "</div>";
        return;
      }
      render();
    }
    function guard(f) {
      try { f(); } catch (e) {
        if (e instanceof NotModelled) { m.fault = "not modelled on this page: " + e.message; render(); }
        else throw e;
      }
    }
    $("int-reset").addEventListener("click", reset);
    $("int-args").addEventListener("keydown", function (ev) { if (ev.key === "Enter") reset(); });
    $("int-step").addEventListener("click", function () { guard(function () { m.step(); render(); }); });
    $("int-run").addEventListener("click", function () {
      guard(function () { var n = 0; while (m.step()) if (++n > 100000) { m.fault = "out of fuel (this page)"; break; } render(); });
    });
    reset();
  }

  // ---------------------------------------------------------------- E: environment explorer
  function parseEnv(src, defaultNs) {
    var rows = [], ns = defaultNs, data = null, inDoc = false;
    function flushData() {
      if (!data) return;
      var succ = data.ctors.map(function (c) { return "(^" + c.name + (c.fields ? " " + c.fields : "") + ")"; }).join(" ");
      rows.push({ kind: "terminal (from the datatype)", lean: data.name + ".case", env: ns + "." + data.name + ".case",
        sig: "terminal insn " + data.name + ".case (scrutinee : " + data.name + ") " + succ, ctorOf: null });
      data = null;
    }
    src.split("\n").forEach(function (raw) {
      var line = raw.trim(), m;
      if (inDoc) { if (/-\/\s*$/.test(line)) inDoc = false; return; }
      if (/^\/--/.test(line)) { if (!/-\/\s*$/.test(line)) inDoc = true; return; }
      if (!line || /^--/.test(line)) return;
      if ((m = /^\|\s*(?:\/--.*?-\/\s*)?([\w«»]+)\s*(.*)$/.exec(line)) && data) {
        var cn = m[1].replace(/[«»]/g, "");
        data.ctors.push({ name: cn, fields: m[2] });
        rows.push({ kind: "constructor", lean: data.name + "." + cn, env: ns + "." + cn, sig: "| " + cn + (m[2] ? " " + m[2] : "") + "   (of " + data.name + ")" });
        return;
      }
      flushData();
      if ((m = /^namespace (\S+)/.exec(line))) { ns = m[1].replace(/[«»]/g, ""); return; }
      if (/^(open|end|public environment)/.test(line)) return;
      if ((m = /^data (\w+)/.exec(line))) { data = { name: m[1], ctors: [] }; rows.push({ kind: "data", lean: m[1], env: ns + "." + m[1], sig: line }); return; }
      if ((m = /^type (\w+)/.exec(line))) { rows.push({ kind: "type", lean: m[1], env: ns + "." + m[1], sig: line }); return; }
      if ((m = /^abbrev (\w+)/.exec(line))) { rows.push({ kind: "abbrev", lean: m[1], env: ns + "." + m[1], sig: line }); return; }
      if ((m = /^(terminal )?insn ([\w«»]+)(?: as "(\w+)")?/.exec(line))) {
        var ln = m[2].replace(/[«»]/g, "");
        rows.push({ kind: m[1] ? "terminal" : "insn", lean: ln, env: ns + "." + (m[3] || ln), sig: line });
        return;
      }
      // continuation of a signature
      if (rows.length && /^[:(]/.test(line)) rows[rows.length - 1].sig += " " + line;
    });
    flushData();
    return rows;
  }
  function printedNames(row) {
    var n = row.env;
    if (n === "base.jump") return ["jump", "ret"];
    if (n === "base.branch") return ["branch"];
    if (n === "base.unreachable") return ["unreachable"];
    return [n];
  }
  function initEnv() {
    var root = $("w-env"), d = data("doc-env"), src = data("doc-source"), reg = data("doc-cfg");
    var rows = parseEnv(d.whileSource, "while").map(function (r) { r.from = "While"; return r; });
    var base = parseEnv(d.baseSource, "base").filter(function (r) { return d.baseUsed.indexOf(r.env) >= 0; });
    base.forEach(function (r) { r.from = "Base"; });
    rows = rows.concat(base);
    rows.forEach(function (r) {
      if (r.from === "While") r.rule = d.rules[r.lean] || (r.kind === "constructor" ? "(no rule: a constructor)" : r.kind.indexOf("from the datatype") >= 0 ? "(no rule: the datatype's case)" : r.kind === "type" || r.kind === "data" || r.kind === "abbrev" ? d.types[r.lean] || "" : "");
      else r.rule = d.baseRules[r.env] || "";
    });
    var regionText = reg.filter(function (t) { return t.id === "region"; })[0].text;
    var p1 = linesInto($("env-m1"), "dyn", src.dynFolded), p2 = linesInto($("env-m2"), "dyn", regionText);
    var html = '<table class="envtable"><thead><tr><th scope="col">Name</th><th scope="col">Kind</th><th scope="col">Signature, as written</th><th scope="col">Rule</th></tr></thead><tbody>';
    rows.forEach(function (r, i) {
      html += '<tr data-i="' + i + '"><td><button type="button" aria-pressed="false" data-i="' + i + '">' + esc(r.env) + "</button></td><td>" + esc(r.kind) + (r.from === "Base" ? " (base)" : "") +
        '</td><td class="sig">' + highlight("lean", r.sig) + "</td><td>" + (r.rule ? '<pre class="lean">' + highlight("lean", r.rule) + "</pre>" : "") + "</td></tr>";
    });
    html += "</tbody></table>";
    $("env-table-wrap").innerHTML = html;
    var status = $("env-status");
    function mark(els, text, names) {
      var count = 0;
      text.split("\n").forEach(function (l, i) {
        var hit = names.some(function (n) {
          var re = new RegExp("(^|[\\s=])" + n.replace(/\./g, "\\.") + "(?=[\\[(\\s]|$)");
          return re.test(l);
        });
        els[i].classList.toggle("hl", hit); if (hit) count++;
      });
      return count;
    }
    $("env-table-wrap").addEventListener("click", function (ev) {
      var b = ev.target.closest("button[data-i]"); if (!b) return;
      var i = +b.getAttribute("data-i"), r = rows[i];
      var btns = $("env-table-wrap").querySelectorAll("button[data-i]"), trs = $("env-table-wrap").querySelectorAll("tr[data-i]");
      for (var k = 0; k < btns.length; k++) { btns[k].setAttribute("aria-pressed", String(k === i)); trs[k].classList.toggle("sel", k === i); }
      var names = printedNames(r);
      var c1 = mark(p1, src.dynFolded, names), c2 = mark(p2, regionText, names);
      status.textContent = r.env + ": " + c1 + " line" + (c1 === 1 ? "" : "s") + " in the running example, " + c2 + " in the region variant.";
    });
    reveal(root);
    status.textContent = "Select a name to highlight its uses.";
  }

  // ---------------------------------------------------------------- F: builder trace
  function initTrace() {
    var root = $("w-trace"), d = data("doc-trace"), src = data("doc-source");
    var mean = funcSlice(src.dynFolded, "mean").split("\n");
    var list = $("trace-list"), items = list.querySelectorAll("li"), pre = $("trace-print"), cur = 0;
    var errs = [];
    var names = {};
    (src.dynFolded.match(/[%^]?[\w]+\.\d+/g) || []).forEach(function (n) { names[n.replace(/^\^/, "")] = true; });
    d.forEach(function (t, i) {
      (t.result.match(/%[\w]+\.\d+/g) || []).forEach(function (n) {
        if (!names[n] && !/^%k\./.test(n)) errs.push(n);
      });
    });
    function set(i) {
      cur = i;
      for (var k = 0; k < items.length; k++) { items[k].classList.toggle("cur", k === i); items[k].style.fontWeight = k === i ? "700" : ""; }
      var finished = i === d.length - 1;
      var shown = finished ? mean : mean.slice(0, d[i].upto);
      linesInto(pre, "dyn", shown.join("\n"));
      $("trace-count").textContent = "Call " + (i + 1) + " of " + d.length + (errs.length ? " (name check failed: " + errs.join(", ") + ")" : "");
      $("trace-prev").disabled = i === 0; $("trace-next").disabled = i === d.length - 1;
    }
    $("trace-prev").addEventListener("click", function () { if (cur > 0) set(cur - 1); });
    $("trace-next").addEventListener("click", function () { if (cur < d.length - 1) set(cur + 1); });
    reveal(root);
    set(0);
  }

  // ---------------------------------------------------------------- page
  function printSupport() {
    var opened = [];
    window.addEventListener("beforeprint", function () {
      var ds = document.querySelectorAll("details:not([open])");
      for (var i = 0; i < ds.length; i++) { ds[i].open = true; opened.push(ds[i]); }
    });
    window.addEventListener("afterprint", function () { opened.forEach(function (d) { d.open = false; }); opened = []; });
  }
  function start() {
    [["w-stepper", initStepper], ["w-fold", initFold], ["w-cfg", initCfg], ["w-interp", initInterp], ["w-env", initEnv], ["w-trace", initTrace]]
      .forEach(function (w) {
        var root = $(w[0]); if (!root) return;
        try { w[1](); } catch (e) { fail(root, e && e.message ? e.message : String(e)); if (window.console) console.error(e); }
      });
    printSupport();
  }
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", start); else start();
})();
