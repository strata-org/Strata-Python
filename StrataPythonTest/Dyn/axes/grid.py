#!/usr/bin/env python3
"""Write the axis grid's programs: one program per case of `catalog.py`.

    python3 grid.py OUTDIR            write OUTDIR/<id>.py for each case, and print
                                      `<id> | <group> | <axis> | <expected outcome>` per line
    python3 grid.py --digest OUTDIR   print the SHA-256 of the programs in OUTDIR (written by the
                                      first form) and of `trace.py`, with the string "3.12"

Beside each program `<id>.py`, it writes `<id>.null.py`, the same program with the operation
replaced by `r = None`. CPython's output of the two must differ, or the case observes nothing
that its operation does (the build test checks this when it updates).

The programs are the same on every run: there is no randomness, and the order is the catalog's.
Each program defines `_mark`, `ev`, `show` and `_exc` (the prelude), then runs its case inside
one `try`: the classes, the values, `_mark("op", id)`, the operation, `show(r)`; the `except`
prints the exception with `_exc`; then `_mark("done", id)`. So CPython's output shows whether the
operation ran (`@op`), how it ended (a `=` line or a `!` line), and every user call (`ev` lines)
in order.
"""

import hashlib
import pathlib
import re
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import catalog  # noqa: E402

HERE = pathlib.Path(__file__).resolve().parent
TRACE_PY = HERE.parent / "trace.py"

PRELUDE = '''\
def _mark(kind, i):
    print("@" + kind, i)


def ev(name):
    print("ev", name)


_EXACT = (int, bool, float, str, bytes, range)
_CONTAINERS = (list, tuple, set, frozenset, dict)


def _seen_in(v, seen):
    for s in seen:
        if s is v:
            return True
    return False


def _depth(r):
    """The largest nesting depth of exact containers in `r`: a number up to 50, or "deep" past
    depth 50, or "large" past 300 containers (each container entered once, compared with `is`)."""
    seen = []
    best = 0
    stack = [(r, 1)]
    while stack:
        v, d = stack.pop()
        if _seen_in(v, seen):
            continue
        seen.append(v)
        if len(seen) > 300:
            return "large"
        if d > best:
            best = d
        if best > 50:
            return "deep"
        items = list(v.values()) if type(v) is dict else list(v)
        for w in items:
            if type(w) in _CONTAINERS:
                stack.append((w, d + 1))
    return best


def _builtin_base(v):
    for b in type(v).__mro__:
        if b in _EXACT or b in _CONTAINERS:
            return b
    return None


def _render(v, seen, depth):
    if v is None or type(v) in _EXACT:
        return repr(v)
    if type(v) in _CONTAINERS:
        if _seen_in(v, seen):
            return "..."
        if depth >= 3:
            dv = _depth(v)
            if dv == "deep":
                return type(v).__name__ + " of length " + str(len(v)) + ", nested deeper than 50"
            if dv == "large":
                return type(v).__name__ + " of length " + str(len(v)) + ", holding more than 300 containers"
            return type(v).__repr__(v)
        inner = seen + [v]
        if type(v) is dict:
            parts = [_render(k, inner, depth + 1) + ": " + _render(w, inner, depth + 1)
                     for k, w in v.items()]
            return "{" + ", ".join(parts) + "}"
        parts = [_render(w, inner, depth + 1) for w in v]
        if type(v) in (set, frozenset):
            parts = sorted(parts)
            return type(v).__name__ + "({" + ", ".join(parts) + "})"
        if type(v) is tuple:
            return "(" + ", ".join(parts) + ("," if len(parts) == 1 else "") + ")"
        return "[" + ", ".join(parts) + "]"
    if type(v).__name__ in ("function", "builtin_function_or_method", "method",
                            "method-wrapper", "wrapper_descriptor", "method_descriptor"):
        return "<" + type(v).__name__ + ">"
    b = _builtin_base(v)
    if b is not None:
        return type(v).__name__ + "<" + b.__repr__(v) + "> " + repr(v)
    return type(v).__name__ + " " + repr(v)


def show(r):
    print("=", type(r).__name__, _render(r, [], 0))


def _self(x):
    # A set's repr walks it with `__iter__`, which a subclass may override; `frozenset(x)` reads
    # its members directly.
    shown = frozenset(x) if isinstance(x, (set, frozenset)) else x
    print("self", type(x).__name__, _render(shown, [], 0))


def _is(b):
    print("is", b)


def _exc(e):
    c = e.__cause__
    x = e.__context__
    print("!", type(e).__name__ + ":", str(e), "| cause", type(c).__name__ if c is not None
          else "-", "| context", type(x).__name__ if x is not None else "-", "| suppress",
          e.__suppress_context__)


'''


DEF = re.compile(r"^(\s*)def (__\w+__)\(")
CLASS = re.compile(r"^\s*class (\w+)")
QUIET = {"__repr__", "__init__"}


def with_events(source):
    """`source` with an `ev('<Class>.<name>')` call as the first line of every user dunder that
    lacks one, `__repr__` and `__init__` left out."""
    lines = source.rstrip("\n").split("\n")
    out = []
    cls = "?"
    for i, l in enumerate(lines):
        out.append(l)
        m = CLASS.match(l)
        if m:
            cls = m.group(1)
        m = DEF.match(l)
        if m and m.group(2) not in QUIET and l.rstrip().endswith(":"):
            nxt = lines[i + 1] if i + 1 < len(lines) else ""
            if "ev(" not in nxt:
                out.append(f"{m.group(1)}    ev('{cls}.{m.group(2)}')")
    return "\n".join(out) + "\n"


def indent(text, n=4):
    pad = " " * n
    return "\n".join(pad + l if l.strip() else l for l in text.rstrip("\n").split("\n"))


def render(case, null=False):
    """The program of one case; with `null`, its operation is replaced by `r = None`."""
    body = []
    for c in case.classes:
        body.append(indent(with_events(c)))
    for s in case.setup:
        body.append(indent(with_events(s) if "def " in s else s))
    body.append(indent(f'_mark("op", "{case.id}")'))
    for s in (["r = None"] if null else case.op):
        body.append(indent(s))
    body.append(indent("show(r)"))
    if case.ident:
        body.append(indent(f"_is(r is {case.ident})"))
    tail = f"_self({case.receiver})\n" if case.receiver else ""
    # The receiver is shown after the `try`, so also after a call that raises.
    return (PRELUDE + "try:\n" + "\n".join(body) + "\nexcept Exception as _e:\n    _exc(_e)\n"
            + tail + f'_mark("done", "{case.id}")\n')


def write(outdir):
    out = pathlib.Path(outdir)
    out.mkdir(parents=True, exist_ok=True)
    for old in out.glob("*.py"):
        old.unlink()
    for case in catalog.all_cases():
        (out / f"{case.id}.py").write_text(render(case))
        (out / f"{case.id}.null.py").write_text(render(case, null=True))
        print(f"{case.id} | {case.group} | {case.axis} | {case.expect}")


def digest(outdir):
    h = hashlib.sha256()
    h.update(b"3.12\n")
    h.update(TRACE_PY.read_bytes())
    for f in sorted(pathlib.Path(outdir).glob("*.py")):
        if f.name.endswith(".null.py"):
            continue
        h.update(f.name.encode() + b"\n")
        h.update(f.read_bytes())
    print(h.hexdigest())


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--digest":
        digest(sys.argv[2])
    elif len(sys.argv) == 2:
        write(sys.argv[1])
    else:
        sys.exit(__doc__)
