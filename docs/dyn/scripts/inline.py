"""Inline a static page's local CSS, JS and url() assets into one HTML file."""
import base64, mimetypes, pathlib, re, sys
src = pathlib.Path(sys.argv[1]); out = pathlib.Path(sys.argv[2])
root = src.parent
mimetypes.add_type("font/woff2", ".woff2")

def data_uri(base, ref):
    p = (base / ref.split("?")[0].split("#")[0]).resolve()
    if not p.is_file(): return None
    mt = mimetypes.guess_type(p.name)[0] or "application/octet-stream"
    return f"data:{mt};base64," + base64.b64encode(p.read_bytes()).decode()

def fix_css(css, base):
    def rep(m):
        ref = m.group(2)
        if ref.startswith(("data:", "#", "http")): return m.group(0)
        u = data_uri(base, ref)
        return f'url("{u}")' if u else m.group(0)
    return re.sub(r'url\((["\']?)([^)"\']+)\1\)', rep, css)

html = src.read_text(encoding="utf-8")
missing = []
def link(m):
    href = m.group(1)
    p = root / href
    if not p.is_file():
        missing.append(href); return ""
    return "<style>" + fix_css(p.read_text(encoding="utf-8"), p.parent) + "</style>"
html = re.sub(r'<link rel="stylesheet" href="([^":]+)"[^>]*>', link, html)
def script(m):
    s = m.group(1); p = root / s
    if not p.is_file():
        missing.append(s); return m.group(0)
    body = p.read_text(encoding="utf-8").replace("</script", "<\\/script")
    body = re.sub(r"//# sourceMappingURL=\S+", "", body)
    return "<script>" + body + "</script>"
html = re.sub(r'<script src="([^":]+)"[^>]*></script>', script, html)
html = fix_css(html, root)  # url() in inline <style> blocks
html = re.sub(r'(<img[^>]*src=")([^":]+)(")', lambda m: m.group(1) + (data_uri(root, m.group(2)) or m.group(2)) + m.group(3), html)
# Links back to the page itself: stay on it.
html = html.replace('href="./"', 'href="#"').replace('href="index.html"', 'href="#"')
out.write_text(html, encoding="utf-8")
left = re.findall(r'(?:href|src)="(?!#|data:|https?:|mailto:)([^"]+)"', html)
remaining = sorted(set(left))
print("missing:", missing); print("remaining local refs:", remaining[:20])
if missing or remaining:
    sys.exit(f"inline.py: unresolved local references: {missing + remaining}")
