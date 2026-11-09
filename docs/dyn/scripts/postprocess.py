"""Make Verso's HTML output work offline and from file://.

Usage: python3 -I scripts/postprocess.py DIR    (DIR is an html-multi or html-single output folder)

1. Drop Verso's trailing-slash redirect (the first <script> in <head> sends a URL that ends
   in neither `/` nor `.html` to `URL/`, which from file:// is a directory listing). Drop the
   CDN <script> for marked.js that Verso's page template hard-codes (it renders Markdown
   docstrings in Lean hovers and is guarded by `typeof marked`), and the search
   <script>/<link> tags Verso emits even with the search feature off.
2. Point links at files: a link to `dir/` or `dir/#id` opens a directory listing from
   file://, so it becomes `dir/index.html` (or `dir/index.html#id`); the empty home link
   becomes `index.html`. Heading permalinks, which go through Verso's `find/` redirect page,
   link to their target directly, and the then unused `find/` page is removed. A bare `#id`
   on a page below the root would resolve against `<base href>` (the root), so it names its
   own page.
3. If the document has Lean hovers, inline their data: Verso loads it with fetch(), which
   browsers refuse on file://. The shim serves the inline copy on every protocol.
4. Check every `href`/`src`: each must be a same-page anchor or a relative path to a file
   that exists, and none may name a directory. Print what was changed.
"""
import json, pathlib, re, sys
from collections import Counter
from urllib.parse import parse_qs, unquote

changed = Counter()

root = pathlib.Path(sys.argv[1])
pages = sorted(root.rglob("*.html"))

# ---- 2. permalink targets, from Verso's cross-reference database
xref = {}
if (root / "xref.json").exists():
    for domain, d in json.loads((root / "xref.json").read_text(encoding="utf-8")).items():
        for name, entries in d.get("contents", {}).items():
            if entries and "address" in entries[0]:
                a = entries[0]["address"].lstrip("/") or "index.html"
                xref[(domain, name)] = a + ("#" + entries[0]["id"] if entries[0].get("id") else "")

def to_file(href, here):
    """`href` as written on a page at `here` (relative to the root, which is the base)."""
    if re.match(r"^[a-z][a-z0-9+.-]*:", href, re.I) or href.startswith("//"):
        return href
    if href.startswith("#"):
        if here in ids and href[1:] not in ids[here]:
            changed["anchor to a page title (which has no id) dropped"] += 1
            return here
        if here == "index.html":
            return href
        changed["same-page anchor named in full (below <base>)"] += 1
        return here + href
    m = re.match(r"^([^?#]*)(\?[^#]*)?(#.*)?$", href)
    path, query, frag = m.group(1), m.group(2) or "", m.group(3) or ""
    if path.endswith("find/") and query:
        q = parse_qs(query[1:])
        target = xref.get((q.get("domain", [""])[0], q.get("name", [""])[0]))
        if target:
            changed["permalink via find/ to its page and anchor"] += 1
            t = to_file(target, "")
            # On its own page, a permalink is a same-page anchor.
            tp, _, tf = t.partition("#")
            return ("#" + tf) if tp == here and here == "index.html" and tf else t
    if path == "" or path.endswith("/"):
        changed["directory link to its index.html" if path else "empty home link to index.html"] += 1
        path += "index.html"
    # A chapter's own tag names its page, whose title carries no id: link to the page.
    if frag and path in ids and frag[1:] not in ids[path]:
        changed["anchor to a page title (which has no id) dropped"] += 1
        frag = ""
    return path + query + frag

# ---- 3. inline hover data
docs = root / "-verso-docs.json"
shim = None
if docs.exists() and docs.read_text(encoding="utf-8").strip() not in ("", "{}"):
    payload = docs.read_text(encoding="utf-8")
    json.loads(payload)
    payload = payload.replace("</", "<\\/")
    shim = (
        "<script id=\"verso-docs-inline\">(function(){var DOCS=" + payload + ";"
        "var f=window.fetch;"
        "window.fetch=function(u,o){if(typeof u==='string'&&/verso-docs\\.json$/.test(u))"
        "return Promise.resolve(new Response(JSON.stringify(DOCS),{headers:{'Content-Type':'application/json'}}));"
        "return f.apply(this,arguments);};})();</script>\n"
    )

ids = {p.relative_to(root).as_posix(): set(re.findall(r'\bid="([^"]+)"', p.read_text(encoding="utf-8")))
       for p in pages}

for page in pages:
    html = page.read_text(encoding="utf-8")
    here = page.relative_to(root).as_posix()
    # 1. no redirect, no network
    html, n = re.subn(r"[ \t]*<script>\s*\(function\(\)\{\s*const \{protocol:proto.*?</script>\n?", "", html, count=1, flags=re.S)
    changed["trailing-slash redirect script removed"] += n
    html = re.sub(r"[ \t]*<script[^>]*cdn\.jsdelivr\.net/npm/marked[^>]*></script>\n?", "", html)
    html = re.sub(r"[ \t]*<script[^>]*\"-verso-search/[^\"]*\"[^>]*></script>\n?", "", html)
    html = re.sub(r"[ \t]*<link[^>]*\"-verso-search/[^\"]*\"[^>]*>\n?", "", html)
    # 2.
    html = re.sub(r'(<a\b[^>]*?\bhref=")([^"]*)(")',
                  lambda m: m.group(1) + to_file(m.group(2).replace("&amp;", "&"), here).replace("&", "&amp;") + m.group(3),
                  html)
    # 3.
    if shim and 'id="verso-docs-inline"' not in html:
        html = html.replace("</head>", shim + "</head>", 1)
    page.write_text(html, encoding="utf-8")

# The find/ redirect page is unused once permalinks point at their targets.
if (root / "find").is_dir() and not any("find/" in re.sub(r"<script.*?</script>", "", p.read_text(encoding="utf-8"), flags=re.S)
                                         for p in root.rglob("*.html") if p.parent.name != "find"):
    import shutil
    shutil.rmtree(root / "find")
    changed["unused find/ page removed"] += 1
pages = sorted(root.rglob("*.html"))

# ---- 4. every local reference resolves
missing = []
for page in pages:
    html = page.read_text(encoding="utf-8")
    m = re.search(r'<base href="([^"]*)"', html)
    base = (page.parent / (m.group(1) if m else "")).resolve()
    for attr, ref in re.findall(r'<(?!base\b)[a-z]+\b[^>]*?\b(href|src)="([^"]*)"', html):
        if ref == "":
            missing.append(f"{page.relative_to(root)}: empty {attr}")
            continue
        if ref.startswith("#"):
            if f'id="{ref[1:]}"' not in html:
                missing.append(f"{page.relative_to(root)}: {ref} (no such id)")
            continue
        if re.match(r"^([a-z][a-z0-9+.-]*:|//)", ref, re.I):
            continue
        path = unquote(ref.split("#")[0].split("?")[0])
        if not path or path.endswith("/"):
            missing.append(f"{page.relative_to(root)}: {ref} (a directory)")
            continue
        if not (base / path).exists():
            missing.append(f"{page.relative_to(root)}: {ref}")
        elif "#" in ref and path.endswith(".html"):
            frag = ref.split("#", 1)[1]
            if frag and f'id="{frag}"' not in (base / path).read_text(encoding="utf-8"):
                missing.append(f"{page.relative_to(root)}: {ref} (no such id)")
    for ref in re.findall(r'url\("([^"]+)"\)', html):
        if not (base / unquote(ref)).exists():
            missing.append(f"{page.relative_to(root)}: url({ref})")
    if re.search(r"-verso-search", html):
        missing.append(f"{page.relative_to(root)}: still loads the search assets")
if missing:
    print("\n".join(sorted(set(missing))), file=sys.stderr)
    sys.exit("postprocess: unresolved references")
for what, n in sorted(changed.items()):
    print(f"postprocess: {what}: {n}")
print(f"postprocess: {len(pages)} pages in {root}; every href/src is an anchor or an existing file")
