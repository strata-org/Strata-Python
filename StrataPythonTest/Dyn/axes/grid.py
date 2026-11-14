#!/usr/bin/env python3
"""Write the axis grid's programs: one program per case of `catalog.py`.

    python3 grid.py OUTDIR            write OUTDIR/<id>.py for each case, and print one line per
                                      case: `<id> | <group> | <axis> | <expected outcome> |
                                      <template> | <calls> | <entries>`
    python3 grid.py --digest OUTDIR   print the SHA-256 of the programs in OUTDIR (written by the
                                      first form) and of `trace.py`, with the string "3.12"

The last three fields are for the coverage check: the operation's template, a file
`OUTDIR/templates/<template>.py` that holds only the operation, whose translation differs from that
of `OUTDIR/templates/null.py` (`r = None`) by the py.* instructions that the operation adds
(`OUTDIR/templates/scaffold.py` is a whole program around a trivial operation, for the
instructions that every case runs);
the built-in functions and methods that the case calls by name; and the dunder entries that its
operation reaches without a call (`list.__len__` for `len(x)`), with the attributes of `typing` and
`dataclasses` that it reads (`typing.List`). A list is comma-separated, or `-`
when empty.

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

import builtins
import hashlib
import pathlib
import re
import sys

if sys.version_info[:2] != (3, 12):
    sys.exit(f"grid.py needs CPython 3.12, not {sys.version.split()[0]}: the catalog reads the "
             "names of the built-in types from the running interpreter")
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
# Pairwise unequal (`grid.py` checks it), so that one stored member answers at most one probe.
_PROBE = [-1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 20, 77, 99, 2 ** 70, 1.5, 2.5,
          "a", "b", "c", "ab", "k", "q", "u", "w", "x", "y", "z", "zz", b"a", b"b", ("a", 1),
          ("b", 2), None]


class _Spy:
    """Equal to the probe `p`, with its hash; when a set compares a stored member with it, it
    keeps that member, so that the set shows its exact members (`{1}`, `{True}`, `{1.0}`, and
    `{('a', 1)}`, `{('a', True)}` all differ)."""

    def __init__(self, p):
        self.p = p
        self.seen = []

    def __hash__(self):
        return hash(self.p)

    def __eq__(self, o):
        self.seen.append(o)
        return o == self.p
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
        if type(v) in (set, frozenset):
            # A set is shown by membership tests against the values the grid uses, without
            # iterating it; only a set that holds other values is iterated (and sorted).
            hits = []
            for p in _PROBE:
                spy = _Spy(p)
                if spy in v:
                    if len(spy.seen) == 1:
                        o = spy.seen[0]
                        hits.append(type(o).__name__ + " " + _render(o, inner, depth + 1))
                    else:
                        hits.append("? " + repr(p))
            if len(hits) == len(v):
                return type(v).__name__ + " of {" + ", ".join(hits) + "}"
            parts = sorted([_render(w, inner, depth + 1) for w in v])
            return type(v).__name__ + "({" + ", ".join(parts) + "})"
        parts = [_render(w, inner, depth + 1) for w in v]
        if type(v) is tuple:
            return "(" + ", ".join(parts) + ("," if len(parts) == 1 else "") + ")"
        return "[" + ", ".join(parts) + "]"
    if type(v).__name__ in ("function", "builtin_function_or_method", "method",
                            "method-wrapper", "wrapper_descriptor", "method_descriptor",
                            "staticmethod", "classmethod", "property", "super"):
        # Their reprs show addresses.
        return "<" + type(v).__name__ + ">"
    if type(v).__repr__ is object.__repr__:
        # The default repr shows the address.
        return "<" + type(v).__name__ + " object>"
    b = _builtin_base(v)
    if b is not None:
        return type(v).__name__ + "<" + b.__repr__(v) + "> " + repr(v)
    return type(v).__name__ + " " + repr(v)


def show(r):
    print("=", type(r).__name__, _render(r, [], 0))


def _self(x):
    # A set's repr walks it with `__iter__`, which a subclass may override; `frozenset(x)` reads
    # its members directly.
    shown = frozenset(x) if isinstance(x, (set, frozenset)) and type(x) not in (set, frozenset) \
        else x
    print("self", type(x).__name__, _render(shown, [], 0))


def _is(b):
    print("is", b)


def _exc(e):
    c = e.__cause__
    x = e.__context__
    print("!", type(e).__name__ + ":", str(e), "| cause", type(c).__name__ if c is not None
          else "-", "| context", type(x).__name__ if x is not None else "-", "| suppress",
          e.__suppress_context__)


# --- end of the prelude ---
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


# Where CPython goes when a type doesn't define a dunder: truth falls back on `__len__`, an in-place
# operator on the binary one.
FALLBACK = {"__bool__": "__len__", "__iadd__": "__add__", "__ior__": "__or__",
            "__isub__": "__sub__", "__imul__": "__mul__"}


class _Seq:
    """A class with only `__getitem__`, whose iterator is CPython's `iterator` type."""

    def __getitem__(self, i):
        raise IndexError(i)


# The built-in types that `builtins` doesn't name, by the names the model's tables use.
OTHER_TYPES = {"NoneType": type(None), "ellipsis": type(...),
               "NotImplementedType": type(NotImplemented),
               "callable_iterator": type(iter(int, 1)), "iterator": type(iter(_Seq()))}


def resolve(t, d):
    """`<type>.<dunder>` for the built-in type in the MRO of the type named `t` that defines the
    dunder `d` (or its fallback), or `None` if none does (`object`'s truth)."""
    cls = OTHER_TYPES.get(t) or getattr(builtins, t, None)
    if not isinstance(cls, type):
        return None
    while d is not None:
        for c in cls.__mro__:
            if d in vars(c):
                return f"{c.__qualname__}.{d}"
        d = FALLBACK.get(d)
    return None


def check_probes():
    """The probes of the prelude are pairwise unequal."""
    ns = {}
    exec(PRELUDE, ns)
    probes = ns["_PROBE"]
    for i, a in enumerate(probes):
        for b in probes[i + 1:]:
            if a == b:
                sys.exit(f"grid.py: the probes {a!r} and {b!r} are equal")


def field_of(items):
    return ",".join(items) if items else "-"


def write(outdir):
    check_probes()
    out = pathlib.Path(outdir)
    templates = out / "templates"
    templates.mkdir(parents=True, exist_ok=True)
    for old in list(out.glob("*.py")) + list(templates.glob("*.py")):
        old.unlink()
    # The operation replaced by `r = None`, against which each template's instructions count.
    (templates / "null.py").write_text("r = None\n")
    # The program around every operation (the prelude, the `try`, `show`): its instructions run in
    # every case, so they count once any case agrees.
    (templates / "scaffold.py").write_text(render(catalog.Case(
        "scaffold", "", "", "", "", ["r = 1"], receiver="r")))
    for case in catalog.all_cases():
        (out / f"{case.id}.py").write_text(render(case))
        (out / f"{case.id}.null.py").write_text(render(case, null=True))
        text = "\n".join(case.op) + "\n"
        key = hashlib.sha256(text.encode()).hexdigest()[:16]
        (templates / f"{key}.py").write_text(text)

        entries = []
        for (t, d) in case.entries:
            e = resolve(t, d)
            if e is None:
                sys.exit(f"grid.py: {case.id}: no built-in type {t} defines {d}")
            entries.append(e)
        entries += case.reads
        print(f"{case.id} | {case.group} | {case.axis} | {case.expect} | {key} | "
              f"{field_of(case.calls)} | {field_of(entries)}")


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
