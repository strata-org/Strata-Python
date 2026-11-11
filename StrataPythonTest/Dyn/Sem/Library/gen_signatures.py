#!/usr/bin/env python3
"""Write the binding signatures of the library's built-ins, as CPython 3.12 checks their arguments.

Writes `StrataPython/Dyn/Sem/Library/Signatures.lean`: for each built-in function and method of
the library, the `BuiltinSig` that the binder (`Builtins/Bind.lean`) takes, with the
style of its messages. The parameters come from `inspect.signature`; the style is the one whose
messages, as the binder writes them, equal CPython's on every wrong call that the script makes.
A built-in that no style matches (`max`, `str.format`) has a custom parser: its rule writes its
messages itself, and the file lists it in a comment.

It also writes `StrataPythonTest/Dyn/dyn_tests/lib_signatures.py`, a test program with one wrong
call of each built-in in `PINNED`, the ones whose rules bind with these signatures.

Run it with CPython 3.12, from the package root:

    python3.12 StrataPythonTest/Dyn/Sem/Library/gen_signatures.py

With `--check`, it writes nothing and fails if either file differs from its output. Any other
version than 3.12 is refused: the messages are 3.12's.
"""

import inspect
import re
import sys
from pathlib import Path

if sys.version_info[:2] != (3, 12):
    sys.exit(f"gen_signatures.py needs CPython 3.12, not {sys.version.split()[0]}")

ROOT = Path(__file__).resolve().parents[4]
OUT = ROOT / "StrataPython/Dyn/Sem/Library/Signatures.lean"
PROGRAM = ROOT / "StrataPythonTest/Dyn/dyn_tests/lib_signatures.py"

FUNCTIONS = ["getattr", "hasattr", "setattr", "callable", "issubclass", "hash", "abs", "divmod",
             "hex", "any", "all", "sum", "max", "min", "sorted"]
# The methods of the library: the names of the 77 that the programs call, on each type that has
# them, with a sample object to call them on.
METHODS = {
    "str": ("'abc'", ["upper", "join", "split", "lower", "strip", "startswith", "replace", "find",
            "count", "endswith", "translate", "rstrip", "splitlines", "index", "rsplit",
            "isalpha", "capitalize", "ljust", "casefold", "isprintable", "isupper", "lstrip",
            "rindex", "istitle", "format", "expandtabs", "isalnum", "removeprefix", "center",
            "isdigit", "islower", "isspace", "zfill", "isdecimal", "isnumeric", "rfind", "title",
            "isidentifier", "rjust", "removesuffix", "swapcase", "isascii", "partition",
            "maketrans", "encode", "format_map", "rpartition"]),
    "list": ("[1]", ["append", "clear", "pop", "insert", "count", "remove", "sort", "extend",
             "copy", "index", "reverse"]),
    "tuple": ("(1,)", ["count", "index"]),
    "range": ("range(3)", ["count", "index"]),
    "dict": ("{}", ["get", "items", "update", "setdefault", "clear", "pop", "keys", "values",
             "copy", "popitem", "fromkeys"]),
    "set": ("set()", ["add", "update", "clear", "pop", "remove", "copy", "union", "discard",
            "issubset", "intersection", "symmetric_difference", "issuperset", "isdisjoint",
            "difference", "difference_update", "intersection_update",
            "symmetric_difference_update"]),
    "frozenset": ("frozenset()", ["copy", "union", "issubset", "intersection",
                  "symmetric_difference", "issuperset", "isdisjoint", "difference"]),
}
# The built-ins whose rules bind with these signatures (their Lean names), so that
# `lib_signatures.py` calls each of them wrongly once.
PINNED = ["getattr", "hasattr", "setattr", "callable", "issubclass", "hash", "abs", "divmod",
          "hex", "any", "all", "sum"] + [
    f"{t}_{n}" for t in ["str", "list", "tuple", "range", "dict", "set", "frozenset"]
    for n in METHODS[t][1] if (t, n) != ("str", "maketrans")] + ["str_maketrans"]
# `str.maketrans` comes last: the model can't read a static method's table entry yet, so the
# program stops with a gap there.


class Sig:
    """A `BuiltinSig`."""

    def __init__(self, name, qualname, params):
        self.name, self.qualname = name, qualname
        P = inspect.Parameter
        pos = [p for p in params if p.kind in (P.POSITIONAL_ONLY, P.POSITIONAL_OR_KEYWORD)]
        kwonly = [p for p in params if p.kind == P.KEYWORD_ONLY]
        self.posonly = sum(p.kind == P.POSITIONAL_ONLY for p in pos)
        self.minpos = sum(p.default is P.empty for p in pos)
        self.maxpos = len(pos)
        self.kwnames = [p.name for p in pos[self.posonly:]] + [p.name for p in kwonly]
        self.reqkw = sum(p.default is P.empty for p in kwonly)
        self.varargs = any(p.kind == P.VAR_POSITIONAL for p in params)
        self.varkw = any(p.kind == P.VAR_KEYWORD for p in params)
        self.style = None

    def styles(self):
        """The styles that these parameters allow, in the order they are tried."""
        if self.varkw:
            return []
        out = []
        if self.maxpos == 1 and self.minpos == 1 and self.posonly == 1 and not self.kwnames \
                and not self.varargs:
            out.append("methO")
        if self.maxpos == 0 and not self.kwnames and not self.varargs:
            out.append("noArgs")
        if not self.kwnames:
            out.append("posOnly")
            out.append("parseTuple")
        out.append("keywords")
        return out

    def bind(self, style, n, kws):
        """The binder's message for `n` positional arguments and the keywords `kws` (names), or
        None when it binds them; a port of `bindBuiltinArgs`."""
        def plural(k):
            return "" if k == 1 else "s"
        if style == "methO":
            if kws:
                return f"{self.qualname}() takes no keyword arguments"
            if n != 1:
                return f"{self.qualname}() takes exactly one argument ({n} given)"
            return None
        if style == "noArgs":
            if kws:
                return f"{self.qualname}() takes no keyword arguments"
            if n != 0:
                return f"{self.qualname}() takes no arguments ({n} given)"
            return None
        if style == "parseTuple":
            if kws:
                return f"{self.name}() takes no keyword arguments"
            if self.varargs or self.minpos <= n <= self.maxpos:
                return None
            q = "exactly" if self.minpos == self.maxpos else "at least" if n < self.minpos else "at most"
            k = self.minpos if n < self.minpos else self.maxpos
            return f"{self.name}() takes {q} {k} argument{plural(k)} ({n} given)"
        if style == "posOnly":
            if kws:
                return f"{self.qualname}() takes no keyword arguments"
            exact = "" if self.minpos == self.maxpos else None
            if n < self.minpos:
                q = "" if exact == "" else "at least "
                return f"{self.name} expected {q}{self.minpos} argument{plural(self.minpos)}, got {n}"
            if n > self.maxpos and not self.varargs:
                q = "" if exact == "" else "at most "
                return f"{self.name} expected {q}{self.maxpos} argument{plural(self.maxpos)}, got {n}"
            return None
        fname = self.name + "()"
        maxargs = self.posonly + len(self.kwnames)
        npos = min(n, self.maxpos) if self.varargs else n
        if not self.varargs:
            if n + len(kws) > maxargs:
                k = "keyword " if n == 0 else ""
                return f"{fname} takes at most {maxargs} {k}argument{plural(maxargs)} ({n + len(kws)} given)"
            if n > self.maxpos:
                if self.maxpos == 0:
                    return f"{fname} takes no positional arguments"
                q = "at most" if self.minpos < self.maxpos else "exactly"
                return f"{fname} takes {q} {self.maxpos} positional argument{plural(self.maxpos)} ({n} given)"
        minposonly = min(self.posonly, self.minpos)
        if npos < minposonly:
            q = "at least" if minposonly < self.maxpos else "exactly"
            return f"{fname} takes {q} {minposonly} positional argument{plural(minposonly)} ({npos} given)"
        used = 0
        for i in range(npos, maxargs):
            name = "" if i < self.posonly else self.kwnames[i - self.posonly]
            if i >= self.posonly and name in kws:
                used += 1
            elif i < self.minpos or (self.maxpos <= i < self.maxpos + self.reqkw):
                return f"{fname} missing required argument '{name}' (pos {i + 1})"
        if used < len(kws):
            for i in range(self.posonly, npos):
                name = self.kwnames[i - self.posonly]
                if name in kws:
                    return f"argument for {fname} given by name ('{name}') and position ({i + 1})"
            for k in kws:
                if k not in self.kwnames:
                    return f"'{k}' is an invalid keyword argument for {fname}"
        return None

    def probes(self):
        """Wrong calls: the number of positional arguments and the keyword names."""
        out = [(0, []), (self.maxpos + 1, []), (self.minpos, ["zz"])]
        if self.minpos > 0:
            out.append((self.minpos - 1, []))
        if self.minpos > self.posonly and self.kwnames:
            out.append((self.minpos, [self.kwnames[0]]))
        if self.varargs:
            out.append((self.maxpos + 3, []))
        return out

    def lean(self, ident):
        if self.style == "parseTuple":
            fields = [f'name := "{self.name}"']
            if self.minpos:
                fields.append(f"minpos := {self.minpos}")
            if self.maxpos:
                fields.append(f"maxpos := {self.maxpos}")
            if self.varargs:
                fields.append("varargs := true")
            return (f"/-- `{self.qualname}`, parsed by `PyArg_ParseTuple`. -/\n"
                    f"def {ident} : ParseTupleSig :=\n  {{ {', '.join(fields)} }}\n")
        fields = [f'name := "{self.name}"', f'qualname := "{self.qualname}"', f"style := .{self.style}"]
        for k, v in [("posonly", self.posonly), ("minpos", self.minpos), ("maxpos", self.maxpos),
                     ("reqKwOnly", self.reqkw)]:
            if v:
                fields.append(f"{k} := {v}")
        if self.kwnames:
            fields.append("kwnames := #[" + ", ".join(f'"{k}"' for k in self.kwnames) + "]")
        if self.varargs:
            fields.append("varargs := true")
        body = ", ".join(fields)
        return f"/-- `{self.qualname}`. -/\ndef {ident} : BuiltinSig :=\n  {{ {body} }}\n"


def cpython_message(f, n, kws):
    """CPython's `TypeError` message for the call of `f`, or None if it raised none."""
    try:
        f(*([None] * n), **{k: None for k in kws})
    except TypeError as e:
        return str(e)
    except Exception:
        return None
    return None


POSITIONAL = re.compile(r"^\w+ expected (?:at least |at most )?(\d+) arguments?, got \d+$")
PARSE_TUPLE = re.compile(r"^\w+\(\) takes (?:exactly|at least|at most) (\d+) arguments? \(\d+ given\)$")


def guessed_params(f):
    """The positional-only parameters of a built-in without a text signature, as its messages
    give them: none, one, or the bounds of `_PyArg_CheckPositional`'s messages."""
    P = inspect.Parameter
    few, many = cpython_message(f, 0, []), cpython_message(f, 20, [])
    if many and many.endswith("takes no arguments (20 given)"):
        return []
    if few and few.endswith("takes exactly one argument (0 given)"):
        return [P("a", P.POSITIONAL_ONLY)]
    lo = POSITIONAL.match(few or "") or PARSE_TUPLE.match(few or "")
    hi = POSITIONAL.match(many or "") or PARSE_TUPLE.match(many or "")
    if not hi:
        # `METH_VARARGS` without a count, such as `set.union`: any number of arguments, and no
        # keywords.
        kw = cpython_message(f, 0, ["zz"])
        if few is None and kw is not None and kw.endswith("() takes no keyword arguments"):
            return [P("args", P.VAR_POSITIONAL)]
        return None
    minpos = int(lo.group(1)) if lo else 0
    maxpos = int(hi.group(1))
    return [P(f"a{i}", P.POSITIONAL_ONLY, default=P.empty if i < minpos else None)
            for i in range(maxpos)]


def signature(f, name, qualname):
    """The signature of `f`, with its style, or None for a custom parser."""
    guessed = False
    try:
        params = list(inspect.signature(f).parameters.values())
    except (ValueError, TypeError):
        params = guessed_params(f)
        if params is None:
            return None
        guessed = True
    sig = Sig(name, qualname, params)
    # Guessed parameters have no names, so they can't be keyword parameters.
    for style in [st for st in sig.styles() if not (guessed and st == "keywords")]:
        ok = True
        for n, kws in sig.probes():
            want = sig.bind(style, n, kws)
            if want is not None and cpython_message(f, n, kws) != want:
                ok = False
                break
        if ok:
            sig.style = style
            return sig
    return None


def targets():
    """Each built-in: its Lean name, the callable, the name and qualname in its messages."""
    import builtins
    for n in FUNCTIONS:
        yield n, getattr(builtins, n), n, n
    for t, (sample, names) in METHODS.items():
        for n in names:
            yield f"{t}_{n}", getattr(eval(sample), n), n, f"{t}.{n}"


def main():
    sigs, custom = [], []
    for ident, f, name, qualname in targets():
        s = signature(f, name, qualname)
        (sigs.append((ident, s)) if s else custom.append(qualname))
    lines = [
        "/-",
        "  Copyright Strata Contributors",
        "",
        "  SPDX-License-Identifier: Apache-2.0 OR MIT",
        "-/",
        "module",
        "public import StrataPython.Dyn.Sem.Library.ParseTuple",
        "",
        "set_option autoImplicit false",
        "",
        "/-!",
        "# The binding signatures of the library's built-ins",
        "",
        "Generated by `StrataPythonTest/Dyn/Sem/Library/gen_signatures.py` from CPython 3.12; don't",
        "edit it by hand. Each signature's style is the one whose messages equal CPython's on the",
        "script's wrong calls. These built-ins have custom parsers, whose rules write their messages:",
        "",
    ]
    lines += [f"- `{q}`" for q in custom]
    lines += ["-/", "", "namespace StrataPython.Dyn.Sem.Library.Signatures", "",
              "open Builtins", "", "@[expose] public section", ""]
    for ident, s in sigs:
        lines.append(s.lean(ident))
    lines += ["end", "", "end StrataPython.Dyn.Sem.Library.Signatures", ""]
    outputs = {OUT: "\n".join(lines)}
    by_ident = dict(sigs)
    prog = ["# One wrong call of each built-in that binds with a generated signature, with CPython",
            "# 3.12's message. Generated by StrataPythonTest/Dyn/Sem/Library/gen_signatures.py.",
            "def wrong(f, *args, **kwargs):",
            "    try:",
            "        f(*args, **kwargs)",
            "    except TypeError as e:",
            "        print(e.args[0])",
            "", ""]
    exprs = {n: n for n in FUNCTIONS}
    exprs.update({f"{t}_{n}": f"{sample}.{n}" for t, (sample, names) in METHODS.items()
                  for n in names})
    for ident in PINNED:
        s = by_ident.get(ident)
        if s is None:
            continue
        # Too many arguments. One that takes any number has no wrong call whose message is the
        # same in every call form (a keyword's names the type only in a method call).
        if s.varargs:
            continue
        args = ", ".join(["None"] * (s.maxpos + 1))
        prog.append(f"wrong({exprs[ident]}, {args})")
    outputs[PROGRAM] = "\n".join(prog) + "\n"
    if "--check" in sys.argv:
        stale = [str(p.relative_to(ROOT)) for p, text in outputs.items() if p.read_text() != text]
        if stale:
            sys.exit(f"differ from the generator's output: {', '.join(stale)}")
        return
    for p, text in outputs.items():
        p.write_text(text)
    print(f"{len(sigs)} signatures, {len(custom)} custom: {', '.join(custom)}")


if __name__ == "__main__":
    main()
