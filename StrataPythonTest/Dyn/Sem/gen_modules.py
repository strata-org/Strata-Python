"""Writes, from CPython 3.12, what the models of the library modules take from CPython:

* `StrataPython/Dyn/Sem/Modules/Names.lean`: every name of `vars()` of the modelled modules and of
  the classes that their objects reach (the closure under `type()`, `__mro__` and `__class__`), and
  the texts that the models' objects hold (the `str` values of the classes' `vars()`, and the
  docstrings of the objects that the modules make);
* `StrataPythonTest/Dyn/sem_modules/depth_*.py`: for each recursive path of the models, a program
  that runs it at a small nesting depth, and at the largest depth where CPython, run as the
  differential test runs it (`trace.py`), doesn't raise `RecursionError` (or at a fixed large
  depth, for a path where CPython never raises).

Run it from the package root with CPython 3.12. Each probe runs in its own process: deep objects
can crash CPython when they are freed."""
import os, subprocess, sys, tempfile, typing

assert sys.version_info[:2] == (3, 12), "run with CPython 3.12"

ROOT = "."
NAMES = f"{ROOT}/StrataPython/Dyn/Sem/Modules/Names.lean"
PROGRAMS = f"{ROOT}/StrataPythonTest/Dyn/sem_modules"
TRACE = f"{ROOT}/StrataPythonTest/Dyn/trace.py"

# The seeds of the closure: the objects that the models make.
SEEDS = [list[int], int | None, typing.List, typing.List[int], typing.Tuple, typing.Tuple[int],
         typing.Optional, typing.Optional[int], typing.Union[int, str], typing.Required[int],
         typing.Any, typing.ForwardRef("x"), typing.cast, typing.overload,
         typing.TypedDict.__mro_entries__((typing.TypedDict,))[0],
         typing.NamedTuple.__mro_entries__((typing.NamedTuple,))[0],
         type(typing.NamedTuple("P", [("x", int)]).x)]
import dataclasses
@dataclasses.dataclass
class _Probe:
    a: int
SEEDS += [dataclasses.field(), dataclasses.MISSING, dataclasses.FrozenInstanceError,
          dataclasses._HAS_DEFAULT_FACTORY, dataclasses._FIELD, _Probe.__dataclass_params__]
MODULES = [typing, dataclasses]
# The objects whose docstring a model holds, by the name that `Names.lean` gives them.
DOCS = {f"typing.{n}": getattr(typing, n).__doc__
        for n in ["Optional", "Union", "NotRequired", "Required", "TypeGuard", "Tuple"]}
# The model's functions whose CPython object has a `__dict__` (functools.wraps), by the native key
# of the model's function.
FUNCTIONS = {f"typing.{c}.__getitem__": getattr(typing, c).__dict__["__getitem__"]
             for c in ["_SpecialForm", "_SpecialGenericAlias", "_TupleType"]}
FUNCTIONS["dataclasses.__repr__"] = _Probe.__repr__

# Each recursive path: the program's stem, how a level nests `x`, what the program does with the
# nested value, its small depth, the large depth for a path where CPython never raises, and a note
# for the program's comment. The
# hash paths are left out for now: the rules' symbolic hashes of nested values cost more than
# linear time in the nesting, so a run at the large depth doesn't end in reasonable time.
PATHS = [
    ("ga_eq", "list[x]", "print(mk(D) == mk(D))", 1000, None, ""),
    ("ga_repr", "list[x]", "print(len(repr(mk(D))))", 1000, None, ""),
    ("union_eq", "list[x] | None", "print(mk(D) == mk(D))", 300, None,
     "# The rules' check that the arguments are known values follows fewer nested levels than\n"
     "# CPython's limit, so it stops the large depth first, before the C levels run out.\n"),
    ("union_repr", "list[x] | None", "print(len(repr(mk(D))))", 1000, None, ""),
    # Each typing subscription hashes its key, whose __hash__ runs a Python frame per level.
    ("typing_getitem", "List[x]", "mk(D)\nprint(1)", 300, None, ""),
    ("typing_repr", "List[x]", "print(len(repr(mk(D))))", 200, None, ""),
    ("typing_union_repr", "Optional[List[x]]", "print(len(repr(mk(D))))", 100, None, ""),
    ("dataclass_repr", "N(x)", "print(len(repr(mk(D))))", 100, None, ""),
]

# The paths whose values can't be built as deep as CPython's limit (each typing subscription
# hashes its key): each value is built a fixed depth deep, and the program uses it inside a
# recursion of depth D, from a small D to the largest one where CPython doesn't raise. The stem, the
# program that builds A and C, the use, the small D, and the levels. The unions' == is built 100
# deep: deeper, the rules' == overflows the native stack before their frame count stops it.
REC_PATHS = [
    # Two chains that are equal but not identical, built through different cache keys: their ==
    # compares the unions as sets, which hashes each argument.
    ("typing_union_eq", "A = mk(100)\nC = mk2(100)", "A == C", 10,
     "Optional[List[x]] # Union[List[x], None]"),
    ("typing_alias_hash", "A = mk(300)", "{A: 1}[A]", 10, "List[x]"),
]

# The imports of the programs of a path, by its stem's prefix.
HEADERS = {"typing": "from typing import List, Optional, Union\n",
           "dataclass": "from dataclasses import dataclass\n@dataclass\nclass N:\n    c: object\n"}
HI = 12000


def closure():
    classes, todo = {}, [type(s) for s in SEEDS] + [s for s in SEEDS if isinstance(s, type)]
    while todo:
        c = todo.pop()
        key = f"{c.__module__}.{c.__qualname__}"
        if key in classes or c.__module__ == "builtins":
            continue
        classes[key] = c
        todo += list(c.__mro__) + [type(c)]
    return dict(sorted(classes.items()))


def lean_str(t):
    out = []
    for ch in t:
        if ch == "\\": out.append("\\\\")
        elif ch == '"': out.append('\\"')
        elif ch == "\n": out.append("\\n")
        elif ch == "\t": out.append("\\t")
        elif ord(ch) < 32 or ord(ch) > 126: out.append("\\u{%x}" % ord(ch))
        else: out.append(ch)
    return '"' + "".join(out) + '"'


def lean_list(names):
    return "[" + ", ".join(f'"{n}"' for n in names) + "]"


def write_names():
    lines = ["/-", "  Copyright Strata Contributors", "",
             "  SPDX-License-Identifier: Apache-2.0 OR MIT", "-/", "module", "",
             "set_option autoImplicit false", "",
             "/-!", "# The names of the modelled modules and classes",
             "",
             f"Generated by `StrataPythonTest/Dyn/Sem/gen_modules.py` from CPython {sys.version.split()[0]}; do not edit.",
             "Every name of `vars()` of each modelled module and of each class that their objects reach;",
             "a model holds each name or stops with a gap on it.",
             "-/", "", "namespace StrataPython.Dyn.Sem.Modules", "", "@[expose] public section", "",
             "/-- The names of `vars()` of each modelled module, by its name. -/",
             "def moduleNames : List (String × List String) := ["]
    lines += [f'  ("{m.__name__}", {lean_list(sorted(vars(m)))}),' for m in MODULES]
    if MODULES:
        lines[-1] = lines[-1].rstrip(",")
    lines += ["]", "", "/-- The names of `vars()` of each class that the models' objects reach, by its",
              "`module.qualname`. -/", "def classNames : List (String × List String) := ["]
    classes = closure()
    entries = [f'  ("{k}",\n    {lean_list(sorted(vars(c)))})' for k, c in classes.items()]
    lines.append(",\n".join(entries))
    lines += ["]", "", "/-- The `str` values of `vars()` of those classes, by `module.qualname.name`, and the",
              "docstrings of the modules' objects, by `module.name`. -/",
              "def texts : List (String × String) := ["]
    pairs = [(f"{k}.{n}", v) for k, c in classes.items() for n, v in sorted(vars(c).items())
             if type(v) is str] + sorted(DOCS.items())
    lines.append(",\n".join(f"  ({lean_str(k)},\n    {lean_str(v)})" for k, v in pairs))
    lines += ["]", "", "/-- The names of `vars()` of each of the model's functions whose CPython object has a",
              "`__dict__`, by the native key of the model's function; each stops with a gap. -/",
              "def functionNames : List (String × List String) := ["]
    lines.append(",\n".join(f'  ("{k}", {lean_list(sorted(vars(f)))})' for k, f in FUNCTIONS.items()))
    lines += ["]", "", "end", "", "end StrataPython.Dyn.Sem.Modules", ""]
    with open(NAMES, "w") as f:
        f.write("\n".join(lines))


def program(level, use, d, header=""):
    # A level "A # B" makes a second chain, mk2, with B.
    if " # " in level:
        level, level2 = level.split(" # ")
        header += f"def mk2(d):\n    x = int\n    for _ in range(d):\n        x = {level2}\n    return x\n"
    return f"{header}def mk(d):\n    x = int\n    for _ in range(d):\n        x = {level}\n    return x\nD = {d}\n{use}\n"


def outcome(level, use, d, header=""):
    """`RE` when the program at depth `d` raises `RecursionError` under `trace.py`, `ok` when it
    ends normally."""
    return outcome_of(program(level, use, d, header).replace("print(", "("))


def outcome_of(text):
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "probe.py")
        with open(path, "w") as f:
            f.write(text)
        r = subprocess.run([sys.executable, "-I", TRACE, path], capture_output=True, text=True)
    if "--- outcome\nraised RecursionError" in r.stdout: return "RE"
    if "--- outcome\nok" in r.stdout: return "ok"
    return f"crash {r.returncode}"


def write_depths():
    for stem, level, use, small, never, note in PATHS:
        header = HEADERS.get(stem.split("_")[0], "")
        if never is None:
            assert outcome(level, use, HI, header) == "RE", f"{stem}: no RecursionError up to depth {HI}"
            lo, hi = 1, HI
            while lo < hi:
                mid = (lo + hi) // 2
                if outcome(level, use, mid, header) == "RE": hi = mid
                else: lo = mid + 1
            large = lo - 1
            head = ("# CPython raises RecursionError from depth %d on this path; the rules count at least\n"
                    "# as many C levels and Python frames and stop with a gap before: the small depth\n"
                    "# agrees, the large one stops.\n") % lo
        else:
            assert outcome(level, use, never, header) == "ok", f"{stem}: CPython fails at depth {never}"
            large = never
            head = ("# CPython never raises RecursionError on this path; the rules count C levels and stop\n"
                    "# with a gap at their own limit: the small depth agrees, the large one stops.\n")
        text = head + note + program(level, use, small, header) + f"D = {large}\n{use}\n"
        with open(f"{PROGRAMS}/depth_{stem}.py", "w") as f:
            f.write(text)
        print(f"depth_{stem}.py: {small} and {large}")


def rec_program(build, use, d, header, level):
    defs = program(level, "", 0, header).split("D = 0")[0]
    return (f"{defs}{build}\ndef deep(n):\n    if n == 0:\n        return {use}\n"
            f"    return deep(n - 1)\nD = {d}\nprint(deep(D))\n")


def write_rec_depths():
    for stem, build, use, small, level in REC_PATHS:
        header = HEADERS.get(stem.split("_")[0], "")
        probe = lambda d: outcome_of(rec_program(build, use, d, header, level).replace("print(", "("))
        assert probe(HI) == "RE", f"{stem}: no RecursionError up to depth {HI}"
        lo, hi = 1, HI
        while lo < hi:
            mid = (lo + hi) // 2
            if probe(mid) == "RE": hi = mid
            else: lo = mid + 1
        head = ("# CPython raises RecursionError from a recursion of depth %d around this use of a value\n"
                "# built deep; the rules count at least as many Python frames and stop with a gap\n"
                "# before: the small depth agrees, the large one stops.\n") % lo
        text = head + rec_program(build, use, small, header, level) + f"D = {lo - 1}\nprint(deep(D))\n"
        with open(f"{PROGRAMS}/depth_{stem}.py", "w") as f:
            f.write(text)
        print(f"depth_{stem}.py: {small} and {lo - 1}")


# The property that makes the subscription cache's fingerprints sound: two known keys hit the same
# entry exactly when CPython's dict finds it, i.e. when they are ==. Each pair is two keys made of
# the kinds of known values that knownDepth (Types.lean) accepts. In the even pairs, the second key
# equals the first: the same expression rebuilt, with True written as 1, or with a union's two
# arguments swapped. The ints include -1 and -2, and 0 and 2**61 - 1, whose hashes are equal.
KINDS = ["int", "bool", "str", "none", "class", "any", "list_alias", "optional", "dict_alias",
         "tuple_alias", "ga_list", "ga_dict", "union_type", "typing_union", "forward_ref",
         "special_alias", "arg_tuple", "guard"]


def known(rng, depth):
    kind = rng.choice(KINDS if depth > 0 else KINDS[:6])
    sub = lambda: known(rng, depth - 1)
    if kind == "int": return str(rng.choice([0, 1, 2, -1, -2, 2**61 - 1]))
    if kind == "bool": return rng.choice(["True", "False"])
    if kind == "str": return rng.choice(['"a"', '"b"'])
    if kind == "none": return "None"
    if kind == "class": return rng.choice(["int", "str", "bool", "float", "C"])
    if kind == "any": return "Any"
    if kind == "list_alias": return f"List[{sub()}]"
    if kind == "optional": return f"Optional[{sub()}]"
    if kind == "dict_alias": return f"Dict[{sub()}, {sub()}]"
    if kind == "tuple_alias": return f"Tuple[{sub()}, ...]"
    if kind == "ga_list": return f"list[{sub()}]"
    if kind == "ga_dict": return f"dict[{sub()}, {sub()}]"
    if kind == "special_alias": return rng.choice(["List", "Dict"])
    if kind == "arg_tuple": return f"Dict[({sub()}, {sub()})]"
    if kind == "guard": return f"{rng.choice(['TypeGuard', 'Required'])}[{sub()}]"
    if kind == "forward_ref": return f'Optional["{rng.choice(["N", "M"])}"]'
    # Unions take classes, aliases and None only.
    classy = lambda: rng.choice(["int", "str", "C", "None", "list[int]", "List[str]"])
    a = classy()
    b = rng.choice([c for c in ["int", "str", "C", "None", "list[int]", "List[str]"] if c != a])
    if kind == "union_type": return f"({a} | {b})" if "List" not in a + b else f"Union[{a}, {b}]"
    return f"Union[{a}, {b}]"


def equal_variant(rng, src):
    """An expression == to `src`, built another way."""
    out = src.replace("True", "1") if rng.random() < 0.5 else src
    if out.startswith("Union[") and "," in out:
        inner = out[len("Union["):-1].split(", ", 1)
        if len(inner) == 2 and "[" not in inner[0] + inner[1]:
            out = f"Union[{inner[1]}, {inner[0]}]"
    return out


def write_cache_property():
    import random
    rng = random.Random(0)
    lines = ["# Generated by gen_modules.py: equal known keys hit the same typing cache entry, as CPython's",
             "# dict does, and keys that are not == miss.",
             "from typing import Any, Dict, List, Optional, Required, Tuple, TypeGuard, Union",
             "class C:", "    pass"]
    for i in range(120):
        a = known(rng, 2)
        b = equal_variant(rng, a) if i % 2 == 0 else known(rng, 2)
        lines.append(f"print({i}, List[{a}] is List[{b}])")
    # Pairs that are equal only after a union is normalized.
    for a, b in [("Union[int, None]", "Optional[int]"), ("Optional[int]", "int | None"),
                 ("Union[int, str, bytes]", "Union[int, Union[str, bytes]]")]:
        lines.append(f"print(List[{a}] is List[{b}])")
    # Pairs whose hashes are equal but that are not ==: only the == check keeps them apart.
    for a, b in [("-1", "-2"), ("0", "2305843009213693951"), ("Union[-1, str]", "Union[-2, str]"),
                 ("Tuple[-1, ...]", "Tuple[-2, ...]"), ("list[-1]", "list[-2]")]:
        lines.append(f"print(List[{a}] is List[{b}])")
    path = f"{PROGRAMS}/typing_cache_property.py"
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")
    pairs = 128
    run = subprocess.run([sys.executable, "-I", path], capture_output=True, text=True)
    assert run.returncode == 0 and len(run.stdout.splitlines()) == pairs, run.stderr
    print(f"typing_cache_property.py: {pairs} pairs")


def write_namedtuple_defaults(n=1000):
    """A NamedTuple class with many defaulted fields: each is a namespace entry, which the port
    walks once, testing it against the field names."""
    lines = ["# Generated by gen_modules.py: a NamedTuple class with many defaulted fields.",
             "from typing import NamedTuple", "class P(NamedTuple):"]
    lines += [f"    f{i}: int = {i}" for i in range(n)]
    lines += ["print(len(P._fields), P().f0, P().f999, P(f5=7).f5)"]
    with open(f"{PROGRAMS}/namedtuple_many_defaults.py", "w") as f:
        f.write("\n".join(lines) + "\n")
    print(f"namedtuple_many_defaults.py: {n} fields")


def write_dataclass_kw_only(n=1000):
    """A dataclass with many keyword-only defaulted fields: its __init__ looks each default up."""
    lines = ["# Generated by gen_modules.py: a dataclass with many keyword-only defaulted fields.",
             "from dataclasses import dataclass", "@dataclass(kw_only=True)", "class C:"]
    lines += [f"    f{i}: int = {i}" for i in range(n)]
    lines += ["c = C(f3=7)", "print(c.f0, c.f3, c.f999)"]
    with open(f"{PROGRAMS}/dataclass_many_kw_only.py", "w") as f:
        f.write("\n".join(lines) + "\n")
    print(f"dataclass_many_kw_only.py: {n} fields")


write_names()
write_depths()
write_rec_depths()
write_cache_property()
write_namedtuple_defaults()
write_dataclass_kw_only()
