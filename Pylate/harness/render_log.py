"""Log renderer: RENDER_SPEC.md JSON in, self-contained HTML out.

Renders accepted logs as the analysis view (global dispatch table,
per-line residual tables, obligations, state panels) and rejected logs
as a red-railed violation listing. Never imports the analyzer: the log
is the only input, which is what makes rendering replayable on demand.

Usage: python3 render_log.py LOG.json [LOG.json...] [-o out.html]
"""
import html
import json
import sys

from resid_status import render_status

CSS = """
:root{
  --ink:#22272e; --muted:#57606a; --page:#f2f4f7; --card:#ffffff;
  --line:#d8dee4; --accent:#1f5fa8;
  --resolved:#1a7f37; --resolved-bg:#dafbe1;
  --split:#9a6700;  --split-bg:#fff8c5;
  --unknown:#7a3ea0;  --unknown-bg:#f3e8fd;
  --mustraise:#cf222e;  --mustraise-bg:#ffebe9;
  --mono:ui-monospace,SFMono-Regular,Menlo,Consolas,"Liberation Mono",monospace;
  --sans:-apple-system,"Segoe UI","Helvetica Neue",Arial,sans-serif;
}
*{box-sizing:border-box}
body{margin:0;background:var(--page);color:var(--ink);font-family:var(--sans);
     font-size:14px;line-height:1.45}
.wrap{max-width:1060px;margin:0 auto;padding:20px 14px 60px}
h1{font-size:19px;margin:0 0 2px}
h2{font-size:15px;margin:28px 0 8px}
h3{font-size:13px;margin:14px 0 6px;color:var(--muted);
   text-transform:uppercase;letter-spacing:.07em}
.eyebrow{font-size:11px;letter-spacing:.09em;text-transform:uppercase;
         color:var(--muted);margin:0 0 4px}
.stats{color:var(--muted);font-size:12.5px;margin:0 0 10px}
.file{background:var(--card);border:1px solid var(--line);border-radius:8px;
      padding:6px 0;overflow-x:auto}
.row{display:grid;grid-template-columns:3.4em 1fr;align-items:baseline;
     border-left:4px solid transparent;padding:0 10px 0 6px}
.row.s-resolved{border-left-color:var(--resolved)}
.row.s-split{border-left-color:var(--split)}
.row.s-unknown{border-left-color:var(--unknown)}
.row.s-mustraise{border-left-color:var(--mustraise)}
.ln{color:var(--muted);font-family:var(--mono);font-size:12px;text-align:right;
    padding-right:10px;user-select:none}
.src{margin:0;font-family:var(--mono);font-size:13px;white-space:pre}
.ann{margin:2px 0 6px 3.4em;padding:0 10px 0 10px}
.badge{display:inline-block;font-family:var(--sans);font-size:10.5px;
       font-weight:600;letter-spacing:.04em;border-radius:4px;
       padding:1px 6px;margin-right:6px;vertical-align:1px}
.b-resolved{color:var(--resolved);background:var(--resolved-bg)}
.b-split{color:var(--split);background:var(--split-bg)}
.b-unknown{color:var(--unknown);background:var(--unknown-bg)}
.b-mustraise{color:var(--mustraise);background:var(--mustraise-bg)}
.b-mayraise{color:var(--split);background:var(--split-bg)}
.b-unreachable{color:var(--muted);background:var(--page);font-style:italic}
.b-plain{color:var(--muted);background:var(--page)}
.oblig{font-family:var(--mono);font-size:12.5px;color:var(--unknown);margin:2px 0}
.oblig.hard{color:var(--mustraise)}
.viol{font-family:var(--mono);font-size:12.5px;color:var(--mustraise);margin:2px 0}
details.state{margin:3px 0 4px}
details.state>summary{cursor:pointer;font-family:var(--mono);font-size:12px;
        color:var(--accent);white-space:nowrap;overflow:hidden;
        text-overflow:ellipsis;max-width:100%}
table{border-collapse:collapse;margin:6px 0 8px;font-size:12.5px;width:100%}
caption{text-align:left;font-size:11px;letter-spacing:.08em;
        text-transform:uppercase;color:var(--muted);padding:4px 0}
th,td{border:1px solid var(--line);padding:3px 8px;text-align:left;
      vertical-align:top}
th{background:var(--page);font-weight:600;font-size:11.5px}
td{font-family:var(--mono);font-size:12px}
td.k-code{color:var(--resolved)}
td.init-ok{color:var(--resolved)}
td.init-maybe{color:var(--split)}
td.init-no{color:var(--mustraise);font-weight:600}
td.must{color:var(--resolved);font-weight:600}
td.may{color:var(--split)}
td.k-raise{color:var(--mustraise);font-weight:600}\n.ctx{color:var(--accent);font-size:11px;font-weight:600}
td.k-deferred{color:var(--unknown)}
.outv{color:var(--muted)}
tbody tr:nth-child(even){background:#fafbfc}
.footer{background:var(--card);border:1px solid var(--line);border-radius:8px;
        padding:8px 12px;margin:10px 0 26px;font-size:12.5px}
.footer .k{color:var(--muted)}
.legend{background:var(--card);border:1px solid var(--line);border-radius:8px;
        padding:10px 12px;margin:12px 0;color:var(--muted);font-size:12.5px}
"""

RANK = {"MUST_RAISE": 4, "UNKNOWN": 3, "SPLIT": 2, "MAY_RAISE": 2, "RESOLVED": 1,
        "UNREACHABLE": 0, "": 0}
CLS = {4: "s-mustraise", 3: "s-unknown", 2: "s-split", 1: "s-resolved", 0: ""}
HARD = {"definitely-unbound", "init-missing", "shape-break",
        "param-annotation-violated"}
DERIVED = {"case-split", "error-guard", "guaranteed-error",
           "deferred-dispatch"}
#: Left halves of an error row that are markers rather than receiver types.
PSEUDO_TAGS = {"code": "from callee"}


def esc(s):
    return html.escape(str(s), quote=True)


def badge(status):
    """The status comes from `resid_status.render_status`, the one derivation
    shared with the analyzer's report, so no label is invented here: an empty
    status prints nothing rather than falling back to a fixed word."""
    if not status:
        return ""
    key = "SPLIT" if status.startswith("SPLIT") else status
    cls = {"MUST_RAISE": "b-mustraise", "UNKNOWN": "b-unknown", "SPLIT": "b-split",
           "RESOLVED": "b-resolved", "MAY_RAISE": "b-mayraise",
           "UNREACHABLE": "b-unreachable"}.get(key, "b-plain")
    return f"<span class='badge {cls}'>{esc(status)}</span>"


def fmt_loc(l):
    cls = l["cls"]
    for pre in ("obj:", "td:"):
        if cls.startswith(pre):
            cls = cls[len(pre):]
    return f"{cls}@{l['site']}{'^' if l['recent'] else '*'}"


def fmt_val(v):
    parts = [t for t in v["tags"]]
    if v["locs"]:
        parts = [t for t in parts
                 if not (t.startswith("obj:") or t in
                         ("list", "dict", "set", "tuple", "range", "gen"))]
        parts.append("{" + ",".join(fmt_loc(l) for l in v["locs"]) + "}")
    if v["funcs"]:
        parts.append("fn{" + ",".join(v["funcs"]) + "}")
    if v["classes"]:
        parts.append("cls{" + ",".join(v["classes"]) + "}")
    return ("|".join(parts) or "BOT") + ("~w" if v.get("witness") else "")


def points_table(points):
    """Every address the analysis recorded a state at.

    The page's state panels are per line, which is the `states` map joined; this
    is the map itself. A key is a program point plus the call frames that reached
    it, so a loop head, a handler entry and the statement that owns them are
    three rows rather than one.
    """
    if not points:
        return ""
    out = ["<details class='state'><summary>program points "
           f"({len(points)}) - the addresses states are keyed by</summary>"
           "<table><thead><tr><th>line</th><th>address</th><th>join</th>"
           "<th>call frames</th></tr></thead><tbody>"]
    for key, p in points.items():
        frames = " &lt; ".join(esc(f) for f in p["frames"]) or "-"
        join = esc(p["join"]) if p["join"] else "-"
        out.append(f"<tr><td>{p['line']}</td><td><code>{esc(key)}</code></td>"
                   f"<td>{join}</td><td><code>{frames}</code></td></tr>")
    out.append("</tbody></table></details>")
    return "".join(out)


def dispatch_table(rows):
    if not rows:
        return ""
    out = ["<h3>Global dispatch table</h3><table><thead><tr>"
           "<th>receiver tag</th><th>operation</th><th>resolves to</th>"
           "</tr></thead><tbody>"]
    for row in sorted(rows, key=lambda r: (r["op"], r["tag"])):
        t = row["target"]
        kind = t["kind"]
        if kind == "code":
            where = f" (line {t['line']})" if "line" in t else ""
            cell = f"<td class='k-code'>{esc(t['label'])}{where}</td>"
        elif kind == "raise":
            cell = f"<td class='k-raise'>raise {esc(t['exc'])}</td>"
        elif kind == "abort":
            cell = f"<td class='k-raise'>abort {esc(t['exc'])}</td>"
        elif kind == "construct":
            cell = f"<td class='k-code'>construct {esc(t['class'])}</td>"
        elif kind == "builtin":
            cell = f"<td>builtin rule {esc(t['rule'])}</td>"
        elif kind == "field":
            # A call always runs code, so `field` on a call row means the
            # emitter mistook a callee's name for a protocol sentinel. Say so
            # instead of publishing "no code runs" about a call.
            if row["op"].startswith("call"):
                cell = ("<td class='k-raise'>inconsistent: call reported as a "
                        "heap cell</td>")
            else:
                cell = "<td>heap cell (no code runs)</td>"
        else:
            cell = "<td class='k-deferred'>deferred to solver</td>"
        # The global table's tag column holds receiver types; `code` is the
        # propagation marker, not a type, so it is named as such here too.
        tag = PSEUDO_TAGS.get(row["tag"])
        shown_tag = f"-- ({tag})" if tag else row["tag"]
        out.append(f"<tr><td>{esc(shown_tag)}</td><td>{esc(row['op'])}</td>"
                   f"{cell}</tr>")
    out.append("</tbody></table>")
    return "".join(out)


def resid_table(rs):
    """One residual table per line: a row per (tag, outcome), each site
    carrying the sub-expression it dispatches on, so a chained expression
    like d[key].field.other_field + x.y decomposes into its getitem,
    getattr, getattr, getattr, and binop sites."""
    out = ["<table><thead><tr><th>status</th><th>sub-expression</th>"
           "<th>operation</th><th>receiver tag</th><th>result</th>"
           "</tr></thead><tbody>"]
    for r in rs:
        st = render_status(r)
        op = f"{r['kind']} {r['desc']}"
        upd = ("[" + "/".join(sorted(r["updates"])) + "]"
               if r["updates"] else "")
        # `expr` is empty on sites the emitter did not attach source text to,
        # and those are exactly the sites that need disambiguating when two
        # share a line, so fall back to the operation's own description.
        src = r.get("expr") or r["desc"]
        if len(src) > 60:
            src = src[:57] + "..."

        def mk_rows(cases, errors):
            rows = [(t, o, False) for t, o in sorted(cases.items())]
            for e in sorted(errors):
                tag, _, outcome = e.partition(" -> ")
                shown = (outcome if outcome.startswith("abort ")
                         else "raise " + outcome)
                # A propagated failure has no receiver type: the left half is
                # the marker `code`, not a tag. Keep the tag column to tags.
                if tag in PSEUDO_TAGS:
                    rows.append(("--", f"{shown} ({PSEUDO_TAGS[tag]})", True))
                else:
                    rows.append((tag, shown, True))
            if rows:
                return rows
            if st == "UNREACHABLE":
                return [("--", "not attempted: an operand raised first",
                         False)]
            return [("", "", False)]

        # a site inlined under more than one call chain shows one slice
        # per invocation; the joined table lives in the global dispatch
        # table at the end of the section
        ctxs = r.get("contexts") or {}
        if len(ctxs) > 1:
            # `updates` is recorded per site, not per invocation, so beside
            # several context slices it cannot be attributed to one of them:
            # showing `[strong]` there would claim a strong update through a
            # may-alias set. It is withheld until the emitter slices it.
            groups = [(f"via {lbl}", mk_rows(s["cases"], s["errors"]),
                       s.get("result"), s.get("updates") or "")
                      for lbl, s in sorted(ctxs.items())]
        else:
            groups = [("", mk_rows(r["cases"], r["errors"]),
                       r.get("result"), upd)]
        first = True
        for lbl, rows, res, group_upd in groups:
            out_val = fmt_val(res) if res and (res["tags"] or res["locs"]) \
                else ""
            group_first = True
            for tag, outcome, is_err in rows:
                cell = (f"<td class='k-raise'>{esc(outcome)}</td>" if is_err
                        else f"<td>{esc(outcome)}</td>")
                head = esc(op + (f" {group_upd}" if group_upd else ""))
                head += (f" <span class='outv'>=&gt; "
                         f"{esc(out_val)}</span>" if out_val else "")
                if lbl and group_first:
                    head = f"<span class='ctx'>{esc(lbl)}</span> " + head
                lead = (f"<td>{badge(st) if first else ''}</td>"
                        f"<td>{esc(src) if first else ''}</td><td>{head}</td>"
                        if group_first else "<td></td><td></td><td></td>")
                out.append(f"<tr>{lead}<td>{esc(tag)}</td>{cell}</tr>")
                group_first = False
                first = False
    out.append("</tbody></table>")
    return "".join(out)


CONTAINER_TAGS = {"list", "dict", "set", "tuple", "range", "gen"}


def init_of(v, kind_tag):
    """RENDER_SPEC section 6: binding status is derived, never stored."""
    tags = v["tags"]
    if kind_tag not in tags:
        return ("bound" if kind_tag == "unbound" else "init"), "init-ok"
    rest = [t for t in tags if t != kind_tag]
    if not rest and not (v["locs"] or v["funcs"] or v["classes"]):
        return (("definitely unbound" if kind_tag == "unbound" else "uninit"),
                "init-no")
    return (("maybe unbound" if kind_tag == "unbound" else "maybe uninit"),
            "init-maybe")


def tags_col(v, drop):
    rest = sorted(t for t in v["tags"] if t not in drop)
    extra = []
    if v["funcs"]:
        extra.append("fn{" + ",".join(sorted(v["funcs"])) + "}")
    if v["classes"]:
        extra.append("cls{" + ",".join(sorted(v["classes"])) + "}")
    return " | ".join(rest + extra) if (rest or extra) else "BOT"


def pts_col(v):
    if not v["locs"]:
        return "-"
    s = "{" + ",".join(fmt_loc(l) for l in v["locs"]) + "}"
    if v.get("witness"):
        s += " (witness: weak stores)"
    return s


def loc_tag(l):
    return l["cls"] if l["cls"].startswith("obj:") else         ("dict" if l["cls"].startswith("td:") else l["cls"])


def alias_col(v):
    locs = v["locs"]
    if not locs:
        return "-", ""
    if len(locs) == 1 and locs[0]["recent"] and not v.get("witness"):
        rest = [t for t in v["tags"] if t not in ("unbound", "uninit")]
        if set(rest) <= {loc_tag(locs[0])}:
            return f"must -> {fmt_loc(locs[0])}", "must"
    return "may", "may"


def value_col(v):
    """The literal bag, as the analysis holds it.

    `1` means the value is exactly that; `1 | 2` means one of two; a trailing `*`
    marks a tag whose values are *not* enumerated, which is the difference
    between "exactly 1" and "an int, possibly 1". A value with no literals and no
    open tag has nothing to say here, so the column shows `-` rather than
    inventing a claim.
    """
    lits = v.get("literals", [])
    # `open` names tags; report it only for tags this value can actually have.
    unknown = [t for t in v.get("open", []) if t in v["tags"]]
    if not lits and not unknown:
        return "-"
    shown = " | ".join(lits)
    if unknown:
        shown = (shown + " | *") if shown else "*"
    return shown


def size_col(v, sizes):
    """The element count of everything this value may point to.

    A count is a property of a *location*, not of the value naming it, so a
    may-alias over two collections of different lengths shows both.
    """
    seen = [sizes[fmt_loc(loc)] for loc in v["locs"]
            if fmt_loc(loc) in sizes]
    if not seen:
        return "-"
    unique = sorted(set(seen))
    return " | ".join(unique)


def state_panel_body(line_state):
    env = line_state.get("env", {})
    heap = line_state.get("heap", [])
    sizes = {fmt_loc(s["loc"]): s["size"]
             for s in line_state.get("sizes", [])}
    rows = []
    for k, v in sorted(env.items()):
        init, icls = init_of(v, "unbound")
        alias, acls = alias_col(v)
        rows.append(
            f"<tr><td>{esc(k)}</td><td>{esc(tags_col(v, {'unbound'}))}</td>"
            f"<td>{esc(value_col(v))}</td>"
            f"<td class='{icls}'>{esc(init)}</td><td>{esc(pts_col(v))}</td>"
            f"<td>{esc(size_col(v, sizes))}</td>"
            f"<td class='{acls}'>{esc(alias)}</td></tr>")
    hrows = []
    for c in heap:
        v = c["val"]
        init, icls = init_of(v, "uninit")
        upd = ("strong (mult 1)" if c["loc"]["recent"] else "weak (summary)")
        ucls = "must" if c["loc"]["recent"] else "may"
        hrows.append(
            f"<tr><td>{esc(fmt_loc(c['loc']))}.{esc(c['field'])}</td>"
            f"<td>{esc(tags_col(v, {'uninit'}))}</td>"
            f"<td>{esc(value_col(v))}</td>"
            f"<td class='{icls}'>{esc(init)}</td><td>{esc(pts_col(v))}</td>"
            f"<td class='{ucls}'>{esc(upd)}</td></tr>")
    body = ""
    if rows:
        body += ("<table><caption>variables</caption><thead><tr>"
                 "<th>variable</th><th>type tags</th><th>value</th>"
                 "<th>init</th><th>points-to</th><th>size</th>"
                 "<th>alias</th></tr></thead><tbody>"
                 + "".join(rows) + "</tbody></table>")
    if hrows:
        body += ("<table><caption>heap (reachable cells)</caption><thead><tr>"
                 "<th>cell</th><th>type tags</th><th>value</th><th>init</th>"
                 "<th>points-to</th><th>update</th></tr></thead><tbody>"
                 + "".join(hrows) + "</tbody></table>")
    return body


def state_panel(line_state, contexts=1):
    """One state per line, which is the join over every context that reaches
    it. `contexts` says how many, because a points-to set of two locations
    from one site is a join artifact where it is more than one, and a genuine
    may-alias where it is one; the panel must not read the same either way."""
    env = line_state.get("env", {})
    summary = "  ".join(f"{k}={fmt_val(v)}" for k, v in sorted(env.items()))
    if len(summary) > 150:
        summary = summary[:150] + "..."
    label = ("entry" if contexts <= 1
             else f"entry (join of {contexts} contexts)")
    return (f"<details class='state'><summary>{label}: "
            f"{esc(summary) or '(empty frame)'}</summary>"
            + state_panel_body(line_state) + "</details>")


def render_section(log):
    out = [f"<h2 id='{esc(log['file'])}'>{esc(log['file'])}</h2>"]
    src = log.get("source") or []
    if log["status"] == "rejected":
        vs = log["violations"]
        by_line = {}
        for v in vs:
            by_line.setdefault(v["line"], []).append(v)
        out.append(f"<p class='stats'>REJECTED: {len(vs)} subset violation"
                   f"{'s' if len(vs) != 1 else ''} (all reported in one pass)"
                   "</p><div class='file'>")
        for i, text in enumerate(src, 1):
            cls = "s-mustraise" if i in by_line else ""
            out.append(f"<div class='row {cls}'><span class='ln'>{i}</span>"
                       f"<pre class='src'>{esc(text) or ' '}</pre></div>")
            for v in by_line.get(i, []):
                out.append(f"<div class='ann'><div class='viol'>[x] "
                           f"[{esc(v['rule'])}] {esc(v['detail'])}</div></div>")
        for v in by_line.get(0, []):
            out.append(f"<div class='ann'><div class='viol'>[x] "
                       f"[{esc(v['rule'])}] {esc(v['detail'])}</div></div>")
        out.append("</div>")
        return "\n".join(out)

    s = log["summary"]
    stats = (f"dispatch sites {s['sites']} | resolved "
             f"{s['devirt']} | deferred to SMT {s['deferred']}")
    pol = log.get("policy")
    if pol:
        modeled = sorted(c for c, m in pol.get("modes", {}).items()
                         if m == "model")
        stats += (f" | abort policy {pol['preset']}"
                  + (f" (modeled: {', '.join(modeled)})" if modeled else
                     " (all machine raises abort)"))
    so = log.get("sorts")
    if so:
        sm = so["summary"]
        stats += (f" | sorts {so['mode']}: {sm['monomorphic']}/"
                  f"{sm['bindings']} monomorphic, {sm['flavors']} flavor"
                  f"{'s' if sm['flavors'] != 1 else ''}")
    out.append(f"<p class='stats'>{esc(stats)}</p>")
    tail = [dispatch_table(log.get("dispatch", [])),
            points_table(log.get("points", {}))]
    if so and (so.get("flavors") or so.get("bindings")):
        rows = ["<h3>flavors</h3><table><thead><tr><th>flavor</th>"
                "<th>variants</th></tr></thead><tbody>"]
        for fl in so.get("flavors", []):
            rows.append(f"<tr><td>{esc(fl['name'])}</td>"
                        f"<td>{esc(', '.join(fl['variants']))}</td></tr>")
        rows.append("</tbody></table><h3>bindings</h3><table><thead><tr>"
                    "<th>carrier</th><th>tags</th><th>sort</th></tr>"
                    "</thead><tbody>")
        for name, b in sorted(so.get("bindings", {}).items()):
            rows.append(f"<tr><td>{esc(name)}</td>"
                        f"<td>{esc('|'.join(b['carrier']))}</td>"
                        f"<td>{esc(b['sort'])}</td></tr>")
        rows.append("</tbody></table>")
        sm = so["summary"]
        tail.append("<details class='state'><summary>sort plan "
                    f"({esc(so['mode'])}): {sm['monomorphic']}/"
                    f"{sm['bindings']} monomorphic, {sm['flavors']} "
                    f"flavors - {esc(so.get('trust', ''))}</summary>"
                    + "".join(rows) + "</details>")
    by_line, obl_by_line, hnd_by_line = {}, {}, {}
    for r in log["residuals"].values():
        by_line.setdefault(r["line"], []).append(r)
    for o in log["obligations"]:
        if o["kind"] not in DERIVED:
            obl_by_line.setdefault(o["line"], []).append(o)
    for tbl in log.get("handlers", {}).values():
        hnd_by_line.setdefault(tbl["line"], []).append(tbl["rows"])
    lines = log.get("lines", {})
    out.append("<div class='file'>")
    for i, text in enumerate(src, 1):
        ranks = [RANK.get("SPLIT" if render_status(r).startswith("SPLIT")
                          else render_status(r), 0) for r in by_line.get(i, [])]
        rank = max(ranks + [0])
        out.append(f"<div class='row {CLS[rank]}'><span class='ln'>{i}</span>"
                   f"<pre class='src'>{esc(text) or ' '}</pre></div>")
        rs = sorted(by_line.get(i, []), key=lambda r: r.get("ord", r["col"]))
        obls = sorted(obl_by_line.get(i, []), key=lambda o: o["kind"])
        hnds = hnd_by_line.get(i, [])
        st = lines.get(str(i))
        if not rs and not obls and st is None and not hnds:
            continue
        out.append("<div class='ann'>")
        if rs:
            out.append(resid_table(rs))
            for r in rs:
                at = r.get("at")
                if at:
                    where = r.get("expr") or r["desc"]
                    out.append("<details class='state'><summary>state at "
                               f"{esc(where)}</summary>"
                               + state_panel_body(at) + "</details>")
        for rows in hnds:
            t = ["<table><thead><tr><th>reaching exception</th>"
                 "<th>handler match</th></tr></thead><tbody>"]
            for row in rows:
                if "caught_by" in row:
                    cb = row["caught_by"]
                    cell = (f"caught by except {esc(cb['clause'])} "
                            f"(line {cb['line']})")
                else:
                    cell = "<span class='k-raise'>propagates</span>"
                t.append(f"<tr><td>{esc(row['exc'])}</td>"
                         f"<td>{cell}</td></tr>")
            t.append("</tbody></table>")
            out.append("".join(t))
        for o in obls:
            hard = " hard" if (o["kind"] in HARD
                              or o["kind"].startswith("abort:")) else ""
            out.append(f"<div class='oblig{hard}'>[!] {esc(o['kind'])}: "
                       f"{esc(o['detail'])}</div>")
        if st is not None:
            nctx = max([len(r.get("contexts") or {}) for r in rs] + [1])
            out.append(state_panel(st, nctx))
        out.append("</div>")
    out.append("</div>")
    out.extend(tail)
    mod = log.get("module", {})
    foot = ["<div class='footer'><span class='eyebrow'>end of module</span>"]
    if mod.get("may_raise"):
        foot.append("<div><span class='k'>may raise (uncaught):</span> "
                    + esc(", ".join(sorted(mod["may_raise"]))) + "</div>")
    if mod.get("unreached"):
        foot.append("<div><span class='k'>never analyzed (no call reached):"
                    "</span> " + esc(", ".join(sorted(mod["unreached"])))
                    + "</div>")
    foot.append("</div>")
    return "\n".join(out + foot)


LEGEND = (
    "<div class='legend'>Rail color = worst residual status on the line "
    "(green RESOLVED, amber SPLIT or MAY_RAISE, purple UNKNOWN, red "
    "MUST_RAISE or subset violation). The global dispatch table lists, per "
    "(receiver tag, operation), the code label the operation resolves to, "
    "or the exception it is guaranteed to raise; <code>abort</code> marks a "
    "machine raise the active policy turns into an assertion failure (no "
    "exceptional continuation is modeled). State panels show the "
    "entry invariant. <code>C@site^</code> is the most-recent block "
    "(strong updates), <code>C@site*</code> the summary (weak updates).</div>")


def main():
    args = sys.argv[1:]
    outpath = "pylate_log_render.html"
    files = []
    i = 0
    while i < len(args):
        if args[i] == "-o":
            outpath = args[i + 1]
            i += 2
        else:
            files.append(args[i])
            i += 1
    body = ["<p class='eyebrow'>pylate</p><h1>Analysis log render</h1>",
            LEGEND]
    for p in files:
        with open(p) as f:
            log = json.load(f)
        if log.get("pylate_log") != 1:
            raise SystemExit(f"{p}: unknown log version "
                             f"{log.get('pylate_log')!r}")
        body.append(render_section(log))
    page = ("<!doctype html><html lang='en'><head><meta charset='utf-8'>"
            "<meta name='viewport' content='width=device-width,"
            "initial-scale=1'><title>pylate log render</title>"
            f"<style>{CSS}</style></head><body>"
            "<div class='wrap'>" + "\n".join(body) + "</div></body></html>")
    with open(outpath, "w") as f:
        f.write(page)
    print(f"wrote {outpath}")


if __name__ == "__main__":
    main()
