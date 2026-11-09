"""Copy the guide's texts from their sources into the places that show them.

Usage: python3 -I scripts/export-data.py [--check] [--package DIR]

The sources are the files in data/ and, for excerpts of the package, the package's own files
(DIR, by default the directory two levels up). From them this script writes:

* widgets/intro-data.js, the data the interactive panels read;
* the listings of DynIntro/Doc.lean that show one of those texts, chosen by language and
  title (LISTINGS below);
* the static copies in widgets/stepper.html, fold.html and trace.html, which readers without
  JavaScript see.

With --check it writes nothing, and fails if any of those differs from what it would write. It
also checks what it does not write: that the excerpts of the package that the guide quotes are
still in the package, that the shorter Dyn and Lean listings are lines of the full texts,
and that the stepper's line patterns and the builder trace's value names match the folded
print.
"""
import html, json, pathlib, re, sys

HERE = pathlib.Path(__file__).resolve().parent.parent
DATA = HERE / "data"


def read(path):
    return path.read_text(encoding="utf-8").rstrip("\n")


def block(text, start, end, what):
    """The lines of `text` from the one that starts with `start` to the one that starts with
    `end`, both included."""
    lines = text.split("\n")
    try:
        i = next(k for k, l in enumerate(lines) if l.startswith(start))
        j = next(k for k in range(i, len(lines)) if lines[k].startswith(end))
    except StopIteration:
        sys.exit(f"export-data: {what}: no block from {start!r} to {end!r}")
    return "\n".join(lines[i:j + 1])


def rule_blocks(text, attr):
    """The rules of `text` registered with `@[dyn_sem <attr>.X]`, by `X`: each from its
    attribute to the line before the next rule, docstring or blank line."""
    rules, key, cur = {}, None, []
    start = f"@[dyn_sem {attr}."
    for line in text.split("\n") + [""]:
        if key is not None and (not line.strip() or line.startswith(start)
                                or line.startswith("/--")):
            rules[key] = "\n".join(cur)
            key = None
        if line.startswith(start):
            key, cur = line[len(start):].split("]", 1)[0], [line]
        elif key is not None:
            cur.append(line)
    return rules


def load(package):
    base = block(read(package / "StrataDyn/Base.lean"), "public environment Base where",
                 "  end base", "StrataDyn/Base.lean")
    while_src = read(package / "StrataDyn/Examples/While/Env.lean")
    while_env = block(while_src, "public environment While extends Base where", "  end «while»",
                      "StrataDyn/Examples/While/Env.lean")
    texts = {
        "source": read(DATA / "mean.while"),
        "folded": read(DATA / "mean.folded.dyn"),
        "full": read(DATA / "mean.full.dyn"),
        "regionSource": read(DATA / "mean-region.while"),
        "regionFolded": read(DATA / "mean-region.folded.dyn"),
        "regionFull": read(DATA / "mean-region.full.dyn"),
        "cells": read(DATA / "mean-cells.dyn"),
        "promoted": read(DATA / "mean-cells.promoted.dyn"),
        "whileEnv": while_env,
        "base": base,
    }
    js = {k: json.loads(read(DATA / f"{k}.json")) for k in ["env", "steps", "outcomes", "trace"]}
    # The rules shown beside the environment are the package's own.
    js["env"]["rules"] = rule_blocks(while_src, "While")
    base_rules = rule_blocks(read(package / "StrataDyn/Exec/Base.lean"), "Base")
    for k, v in base_rules.items():
        js["env"]["baseRules"]["base." + k] = v
    return texts, js


# Listings of Doc.lean that show a text in full: (language, title) -> key of `texts`.
LISTINGS = {
    ("whilelang", "mean.while"): "source",
    ("leantext", "The While environment"): "whileEnv",
    ("dyn", "mean in the cell style (written by hand)"): "cells",
    ("dyn", "mean in the cell style, after ref-to-reg"): "promoted",
    ("whilelang", "mean, with region while"): "regionSource",
    ("dyn", "Printed, folded"): "regionFolded",
    ("leantext", "The base environment (StrataDyn/Base.lean)"): "base",
    ("dyn", "Folded (Module.format)"): "folded",
    ("dyn", "Full (Module.Raw.format .full)"): "full",
}
# Listings that quote a package file: (language, title) -> path, which must contain each of
# their paragraphs.  A listing whose title ends with a path in parentheses, "(StrataDyn/…)"
# or "(StrataDyn/…, name)", quotes that file too.
EXCERPTS = {
    ("leantext", "The function type and its call in the base"): "StrataDyn/Base.lean",
    ("leantext", "While's capabilities"): "StrataDyn/Examples/While/Env.lean",
    ("leantext", "let% and the names it gives"): "StrataDyn/Build/Typed.lean",
    ("leantext", "The While dialect (excerpt)"): "StrataDyn/Examples/While/Dialect.lean",
    ("leantext", "Matching the generated constructors (While's lowering, excerpts)"):
        "StrataDyn/Examples/While/Lower.lean",
    ("dyn", "A class body and its attributes (a Python translator golden)"):
        "StrataPythonTest/Dyn/dyn_tests/e14_nonlocal_class_scope.expected.dyn",
}
# Listings whose lines come from different places of their file, checked line by line.
LINEWISE = {("leantext", "Matching the generated constructors (While's lowering, excerpts)"),
            ("leantext", "The While dialect (excerpt)")}
TITLE_PATH = re.compile(
    r"\(((?:StrataDyn|StrataDynTest|StrataPython|docs)/[\w/.\-]+\.lean)(?:, [^)]*)?\)$")


def excerpt_path(key):
    if key in EXCERPTS:
        return EXCERPTS[key]
    m = TITLE_PATH.search(key[1] or "")
    return m.group(1) if m else None


def quoted(part, text):
    """Whether `part` is in `text`.  A line `…` stands for lines left out, and each run of lines
    between them must be in `text`, consecutive, either as written or with each line's leading
    whitespace removed, so that a listing may quote a program that its file indents."""
    runs, cur = [], []
    for line in part.split("\n"):
        if line.strip() == "…":
            runs.append(cur)
            cur = []
        else:
            cur.append(line)
    runs.append(cur)
    lines = [l.lstrip() for l in text.split("\n")]
    for run in runs:
        if not run or "\n".join(run) in text:
            continue
        want = [l.lstrip() for l in run]
        if not any(lines[i:i + len(want)] == want for i in range(len(lines) - len(want) + 1)):
            return False
    return True


FENCE = re.compile(r'^```(\w+)(?: "((?:[^"\\]|\\.)*)")?\n(.*?)\n```$', re.M | re.S)


def intro_data(texts, js):
    env = js["env"]
    data = {
        "doc-source": {"source": texts["source"], "dynFolded": texts["folded"],
                       "steps": js["steps"]},
        "doc-full": {"dynFolded": texts["folded"], "dynFull": texts["full"]},
        "doc-cfg": [
            {"id": "mean", "title": "mean", "fn": "mean", "text": texts["folded"]},
            {"id": "main", "title": "main", "fn": "main", "text": texts["folded"]},
            {"id": "region", "title": "mean, region while variant", "fn": "mean",
             "text": texts["regionFolded"]},
            {"id": "cells", "title": "mean, in the cell style (written by hand)", "fn": "mean",
             "text": texts["cells"]},
        ],
        "doc-outcomes": js["outcomes"],
        "doc-env": {"whileSource": texts["whileEnv"], "baseSource": texts["base"],
                    "rules": env["rules"], "types": env["types"],
                    "baseRules": env["baseRules"], "baseUsed": env["baseUsed"]},
        "doc-trace": js["trace"],
    }
    return ("// Generated by scripts/export-data.py from data/ and the package sources; "
            "do not edit.\nwindow.DYN_INTRO_DATA = "
            + json.dumps(data, ensure_ascii=False, indent=1) + ";\n")


def doc_listings(doc, texts, package, problems):
    """`doc` with every listing of LISTINGS replaced by its text, and the other checks."""
    seen = set()
    all_dyn = {l.strip() for k in ["folded", "full", "regionFolded", "regionFull", "cells"]
                  for l in texts[k].split("\n")}
    env_lines = {l.strip() for l in texts["whileEnv"].split("\n")}
    rules = set(texts.get("rules", []))

    def repl(m):
        lang, title, body = m.group(1), m.group(2), m.group(3)
        key = (lang, title)
        if key in LISTINGS:
            seen.add(key)
            return f'```{lang} "{title}"\n{texts[LISTINGS[key]]}\n```'
        path = excerpt_path(key)
        if path is not None:
            seen.add(key)
            if not (package / path).is_file():
                problems.append(f"Doc.lean: listing {title!r} quotes {path}, which is not in "
                                f"the package")
                return m.group(0)
            text = (package / path).read_text(encoding="utf-8")
            parts = body.split("\n") if key in LINEWISE else body.split("\n\n")
            for part in parts:
                if part.strip() and not quoted(part, text):
                    problems.append(f"Doc.lean: listing {title!r} is no longer in {path}: "
                                    f"{part.splitlines()[0]}")
        elif lang == "dyn" and title is None:
            for l in body.split("\n"):
                if l.strip() and l.strip() not in all_dyn:
                    problems.append(f"Doc.lean: Dyn line not in any printed text: {l.strip()}")
        elif lang == "leantext" and (title is None or title.startswith("While's rules")):
            chunks = [c for c in body.split("\n\n") if c.strip()]
            for c in chunks:
                c = re.sub(r"^/--.*?-/\n", "", c, flags=re.S)
                first = c.split("\n", 1)[0]
                if first.startswith("insn "):
                    for l in c.split("\n"):
                        if l.strip() not in env_lines:
                            problems.append(f"Doc.lean: line not in the While environment: {l}")
                elif first.startswith("@[dyn_sem"):
                    if c not in rules:
                        problems.append(f"Doc.lean: rule text not in While's Env.lean: {first}")
        return m.group(0)

    out = FENCE.sub(repl, doc)
    for key in list(LISTINGS) + list(EXCERPTS):
        if key not in seen:
            problems.append(f"Doc.lean: no listing {key[0]} {key[1]!r}")
    return out


def pre(htmltext, pre_id, text, what, problems):
    pat = re.compile(r'(<pre\b[^>]*\bid="' + pre_id + r'"[^>]*>)(.*?)(</pre>)', re.S)
    m = pat.search(htmltext)
    if not m:
        problems.append(f"{what}: no <pre id={pre_id}>")
        return htmltext
    return htmltext[:m.start(2)] + html.escape(text, quote=False) + htmltext[m.end(2):]


def trace_list(htmltext, trace, problems):
    pat = re.compile(r'(<ol id="trace-list"[^>]*>)(.*?)(</ol>)', re.S)
    m = pat.search(htmltext)
    if not m:
        problems.append("trace.html: no <ol id=trace-list>")
        return htmltext
    items = "\n".join(f'<li><code>{html.escape(t["call"], quote=False)}</code><br>'
                      f'<span class="note">{html.escape(t["result"], quote=False)}</span></li>'
                      for t in trace)
    return htmltext[:m.start(2)] + items + htmltext[m.end(2):]


def consistency(texts, js, problems):
    lines = texts["folded"].split("\n")
    for i, s in enumerate(js["steps"]):
        for ln, pat in zip(s["lines"], s["match"]):
            if ln >= len(lines) or not re.search(pat, lines[ln]):
                problems.append(f"data/steps.json: step {i + 1}: line {ln} does not match {pat}")
    # The typed `mean` and `main` of Translator 2 print as the folded module; the check file pins
    # its print, and `checks/run.sh` runs it.
    if texts["folded"] not in (HERE / "checks/TypedMean.lean").read_text(encoding="utf-8"):
        problems.append("checks/TypedMean.lean: its pinned print is not data/mean.folded.dyn")
    # Ref-to-reg's listing in Translator 3 is the print that checks/RefToReg.lean pins, of the
    # cell-style module the guide shows.
    r2r = (HERE / "checks/RefToReg.lean").read_text(encoding="utf-8")
    for k, f in [("cells", "mean-cells.dyn"), ("promoted", "mean-cells.promoted.dyn")]:
        if texts[k] not in r2r:
            problems.append(f"checks/RefToReg.lean: its text is not data/{f}")
    names = set(re.findall(r"%\w+\.\d+", texts["folded"]))
    for t in js["trace"]:
        for n in re.findall(r"%\w+\.\d+", t["result"]):
            if n not in names and not n.startswith("%k."):
                problems.append(f"data/trace.json: {n} is not in the folded print")


def main(argv):
    check = "--check" in argv
    package = HERE.parent.parent
    if "--package" in argv:
        package = pathlib.Path(argv[argv.index("--package") + 1])
    texts, js = load(package)
    texts["rules"] = list(js["env"]["rules"].values())
    problems = []
    consistency(texts, js, problems)
    outputs = {HERE / "widgets/intro-data.js": intro_data(texts, js)}
    doc = HERE / "DynIntro/Doc.lean"
    outputs[doc] = doc_listings(doc.read_text(encoding="utf-8"), texts, package, problems)
    st = HERE / "widgets/stepper.html"
    t = pre(st.read_text(encoding="utf-8"), "stp-src", texts["source"], "stepper.html", problems)
    outputs[st] = pre(t, "stp-dyn", texts["folded"], "stepper.html", problems)
    fo = HERE / "widgets/fold.html"
    outputs[fo] = pre(fo.read_text(encoding="utf-8"), "fold-text", texts["folded"], "fold.html",
                      problems)
    tr = HERE / "widgets/trace.html"
    outputs[tr] = trace_list(tr.read_text(encoding="utf-8"), js["trace"], problems)
    stale = [p for p, text in outputs.items()
             if not p.exists() or p.read_text(encoding="utf-8") != text]
    if check:
        problems += [f"{p.relative_to(HERE)} differs from its sources; run scripts/export-data.py"
                     for p in stale]
    else:
        for p in stale:
            p.write_text(outputs[p], encoding="utf-8")
            print(f"export-data: wrote {p.relative_to(HERE)}")
    if problems:
        print("\n".join(problems), file=sys.stderr)
        sys.exit("export-data: failed")
    print("export-data: " + ("everything matches its sources" if check else "done"))


if __name__ == "__main__":
    main(sys.argv[1:])
