#!/usr/bin/env python3
"""Write random programs that combine the axis grid's kinds of input, for the differential runner.

    python3.12 fuzz.py OUTDIR --seed S --count N
    python3.12 fuzz.py --digest OUTDIR   the SHA-256 of the programs in OUTDIR, of `trace.py`, and
                                         of the string "3.12"

writes `OUTDIR/fuzz_<S>_<i>.py` and `fuzz_<S>_<i>.json` (the program's tree) for i < N, and prints
one line per program: `<id> | <bucket> | <steps> | <classes meant to fail>`, where the bucket is
`plain` or `seed` (the program prints, as its last step, the iteration order of a set of strings,
which depends on the hash seed), the steps are the ids of its steps, and the last field lists
the steps that define a class whose creation is meant to raise (`-` for none).

Program `i` of seed `S` draws from `random.Random(f"{S}:{i}")`: a string seed is hashed with
SHA-512, so the stream is the same on every machine and under every `PYTHONHASHSEED`, and program
`i` doesn't depend on `N`.

A program is a list of steps. Each step runs in its own `try`, between `_mark("op", <step>)` and
`_mark("done", <step>)`, and shows its result or exception as the grid's cases do (`grid.py`'s
prelude). The steps: 1 to 4 class definitions (a base, special methods with a behaviour and a
descriptor kind), 2 to 6 values and `SHARED`, a list of them that the re-entering methods
change, and 3 to 12 operations on the values. An operation on an instance whose method
re-enters walks `SHARED` meanwhile. A step that uses a class
whose definition raised prints that it skips.
"""

import json
import pathlib
import random
import sys

if sys.version_info[:2] != (3, 12):
    sys.exit(f"fuzz.py needs CPython 3.12, not {sys.version.split()[0]}")
sys.dont_write_bytecode = True
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import grid  # noqa: E402

BASES = ["object", "int", "str", "list", "dict", "set", "tuple", "float"]
LITERAL = {"object": "", "int": "3", "str": "'ab'", "list": "[1, 2]", "dict": "{'a': 1}",
           "set": "{1}", "tuple": "(1, 2)", "float": "1.5"}

# Special methods, with their parameters and the value a plain behaviour returns.
DUNDERS = {
    "__eq__": ("self, o", "True"), "__hash__": ("self", "7"), "__lt__": ("self, o", "False"),
    "__len__": ("self", "2"), "__iter__": ("self", "iter([1, 2])"), "__bool__": ("self", "True"),
    "__add__": ("self, o", "'add'"), "__radd__": ("self, o", "'radd'"),
    "__getitem__": ("self, k", "7"), "__contains__": ("self, v", "True"),
    "__str__": ("self", "'S'"), "__index__": ("self", "1"), "__format__": ("self, s", "'F'"),
}

# Behaviours of a special method's body.
BEHAVIOURS = {
    "plain": lambda ret: [f"return {ret}"],
    "raise": lambda ret: ["raise ValueError('fz')"],
    "wrong-kind": lambda ret: ["return 'wrong'"],
    "not-impl": lambda ret: ["return NotImplemented"],
    # It changes `SHARED`, a list that the operations also use (bounded to three changes per step).
    "re-enter": lambda ret: ["if len(LOG) < 3:", "    LOG.append(len(LOG))",
                             "    SHARED.append(len(SHARED))", f"return {ret}"],
}

KINDS = ["function", "lambda", "staticmethod", "classmethod", "property", "callable"]

# Operations that use an integer past CPython's limit on the digits of `str` (axis A5): each
# checks it at once, so that the value doesn't only test the limit of `show`.
HUGE = ["{a} < 10 ** 5000", "10 ** 5000 == {a}", "[0][10 ** 5000]",
        "len(str(10 ** 5000))"]

# Operation templates over the values `{a}` and `{b}`.
OPS = ["{a} + {b}", "{a} == {b}", "{a} < {b}", "len({a})", "list({a})", "{a} in {b}",
       "hash({a}) == hash({a})", "bool({a})", "str({a})", "repr({a})", "sorted([{a}, {b}])", "[*{a}]",
       "{{{a}: 1}}", "{a}[0]", "f'{{{a}}}'", "max([{a}, {b}])", "sum([{a}])",
       "[v for v in {a}]", "{a}.__class__.__name__", "isinstance({a}, int)", "[*{a}, *{b}]",
       "tuple({a})", "{a} != {b}", "{a} > {b}", "list(reversed([{a}, {b}]))"] + HUGE

# For each special method, templates whose operation reaches it on the operand `{a}`: an
# operation on an instance of a generated class is drawn among these, so that most such steps
# call the class's methods.
REACHES = {
    "__index__": ["[1, 2, 3][{a}]", "'ab' * {a}", "(1, 2, 3)[{a}:]"],
    "__bool__": ["not {a}", "bool({a})", "1 if {a} else 0"],
    "__radd__": ["{b} + {a}", "1 + {a}", "sum([1, {a}])"],
    "__add__": ["{a} + {b}", "{a} + 1"],
    "__eq__": ["{a} == {b}", "{a} != {b}", "{a} in [{b}, {a}]", "[{a}].count({b})"],
    "__hash__": ["{{{a}: 1}}", "len(set([{a}, {b}]))", "hash({a}) == hash({a})"],
    "__lt__": ["{a} < {b}", "sorted([{a}, {b}])", "max([{a}, {b}])", "min([{b}, {a}])"],
    "__len__": ["len({a})", "bool({a})", "list({a})"],
    "__iter__": ["list({a})", "[*{a}]", "[v for v in {a}]", "tuple({a})", "sorted({a})"],
    "__getitem__": ["{a}[0]", "{a}[1:]", "list({a})"],
    "__contains__": ["{b} in {a}", "1 in {a}"],
    "__str__": ["str({a})", "f'{{{a}!s}}'", "'%s' % ({a},)"],
    "__format__": ["f'{{{a}}}'", "f'{{{a}:>4}}'"],
}

# Literal values, with values at the limits (axis A5).
LITERALS = ["3", "'ab'", "[1, 2]", "{'a': 1}", "(1, 2)", "1.5", "True", "None", "10 ** 30",
            "[[1], [2]]", "{1}", "float('nan')", "-0.0", "''", "()"]


def method_lines(cls, name, kind, behaviour):
    params, ret = DUNDERS[name]
    body = BEHAVIOURS[behaviour](ret)
    # Every user call counts towards a fixed limit (`_tick`), so that a loop that calls user code
    # without end (an iteration over a `__getitem__` that never raises `IndexError`) stops.
    ev = f"ev('{cls}.{name}'); _tick()"
    if kind == "function":
        return [f"    def {name}({params}):", f"        {ev}"] + [f"        {l}" for l in body]
    if kind == "lambda":
        # A lambda holds one expression, so each behaviour but `raise` (which needs a statement,
        # and so stays a `def`) is written as one: the re-entry is the same bounded change of
        # `SHARED` as in the other kinds' bodies.
        if behaviour == "raise":
            return [f"    def {name}({params}):", f"        {ev}", "        raise ValueError('fz')"]
        val = {"plain": ret, "wrong-kind": "'wrong'", "not-impl": "NotImplemented",
               "re-enter": ret}[behaviour]
        change = ("(LOG.append(len(LOG)), SHARED.append(len(SHARED))) if len(LOG) < 3 else None"
                  if behaviour == "re-enter" else "None")
        return [f"    {name} = lambda *a: (ev('{cls}.{name}'), _tick(), {change}, {val})[3]"]
    if kind == "staticmethod":
        return ["    @staticmethod", f"    def {name}(*a):", f"        {ev}"] + [f"        {l}" for l in body]
    if kind == "classmethod":
        return ["    @classmethod", f"    def {name}(cls, *a):", f"        {ev}"] + [f"        {l}" for l in body]
    if kind == "property":
        # The getter runs the behaviour, and the method that it returns gives the result: a
        # `return X` of the body becomes `return lambda *a: X`, and a `raise` raises in the getter.
        out = []
        for l in body:
            if l.lstrip().startswith("return "):
                indent = l[:len(l) - len(l.lstrip())]
                out.append(f"{indent}return lambda *a: {l.lstrip()[len('return '):]}")
            else:
                out.append(l)
        return ["    @property", f"    def {name}(self):", f"        {ev}"] + [f"        {l}" for l in out]
    if kind == "callable":
        return [f"    {name} = _Call_{cls}_{name.strip('_')}()"]
    raise ValueError(kind)


def make(seed, i):
    rnd = random.Random(f"{seed}:{i}")
    tree = {"id": f"fuzz_{seed}_{i}", "classes": [], "values": [], "ops": [],
            "seed_step": rnd.random() < 0.1}
    for k in range(rnd.randint(1, 4)):
        # A class may also subclass the generated class before it (an MRO of user classes).
        earlier = [c["name"] for c in tree["classes"]]
        base = rnd.choice(BASES + earlier[-1:])
        methods = []
        for name in rnd.sample(sorted(DUNDERS), rnd.randint(1, 3)):
            methods.append({"name": name, "kind": rnd.choice(KINDS),
                            "behaviour": rnd.choice(sorted(BEHAVIOURS))})
        # One class in ten holds an attribute whose `__set_name__` raises, so that its creation
        # is meant to raise.
        tree["classes"].append({"name": f"C{k}", "base": base, "methods": methods,
                                "fails": rnd.random() < 0.1})
    names = [c["name"] for c in tree["classes"]]
    for k in range(rnd.randint(2, 6)):
        choice = rnd.random()
        if choice < 0.5:
            c = rnd.choice(tree["classes"])
            lit = LITERAL[root_base(tree, c)]
            tree["values"].append({"name": f"v{k}", "expr": f"{c['name']}({lit})",
                                   "uses": [c["name"]]})
        elif choice < 0.8:
            tree["values"].append({"name": f"v{k}", "expr": rnd.choice(LITERALS), "uses": []})
        else:
            prev = [v["name"] for v in tree["values"]]
            if prev:
                a = rnd.choice(prev)
                tree["values"].append({"name": f"v{k}", "expr": f"[{a}, {a}]", "uses": [a]})
            else:
                tree["values"].append({"name": f"v{k}", "expr": "[]", "uses": []})
    # `SHARED` holds the values that were made (each value step appends its own), and the
    # re-entering methods change it.
    tree["values"].append({"name": "SHARED", "expr": "SHARED", "uses": []})
    vals = [v["name"] for v in tree["values"]]
    by_class = {c["name"]: c for c in tree["classes"]}
    instances = [v for v in tree["values"] if v["uses"] and v["uses"][0] in by_class]
    for k in range(rnd.randint(3, 12)):
        if instances and rnd.random() < 0.7:
            v = rnd.choice(instances)
            m, behaviour = rnd.choice(methods_of(tree, by_class[v["uses"][0]]))
            tmpl = rnd.choice(REACHES.get(m, OPS))
            a = v["name"]
            if behaviour == "re-enter":
                # The method changes `SHARED` while the operation walks it.
                tmpl = "[" + tmpl + " for _ in SHARED]"
        else:
            tmpl = rnd.choice(OPS)
            a = rnd.choice(vals)
        b = rnd.choice(vals)
        uses = [a] + ([b] if "{b}" in tmpl else []) + (["SHARED"] if "SHARED" in tmpl else [])
        tree["ops"].append({"step": f"o{k}", "expr": tmpl.format(a=a, b=b), "uses": uses})
    return tree


def root_base(tree, c):
    """The built-in base of the generated class `c`, through generated bases."""
    by_name = {d["name"]: d for d in tree["classes"]}
    while c["base"] in by_name:
        c = by_name[c["base"]]
    return c["base"]


def methods_of(tree, c):
    """The special methods of `c` and of its generated bases, with their behaviours."""
    by_name = {d["name"]: d for d in tree["classes"]}
    out = [(m["name"], m["behaviour"]) for m in c["methods"]]
    while c["base"] in by_name:
        c = by_name[c["base"]]
        out += [(m["name"], m["behaviour"]) for m in c["methods"]]
    return out


def render(tree):
    """The program of a tree."""
    out = [grid.PRELUDE, "LOG = []", "SHARED = []", "_failed = set()", "_TICKS = [0]",
           "class _Hook:\n    def __set_name__(self, owner, name):\n        ev('_Hook.__set_name__')\n        raise ValueError('set_name')",
           "def _tick():\n    _TICKS[0] += 1\n    if _TICKS[0] > 200:\n        raise RuntimeError('fuzz: too many user calls')"]
    for c in tree["classes"]:
        for m in c["methods"]:
            if m["kind"] == "callable":
                params, ret = DUNDERS[m["name"]]
                body = BEHAVIOURS[m["behaviour"]](ret)
                out.append(f"class _Call_{c['name']}_{m['name'].strip('_')}:")
                out.append("    def __call__(self, *a):")
                out.append(f"        ev('{c['name']}.{m['name']}'); _tick()")
                out += [f"        {l}" for l in body]
    def step(sid, lines, uses, defines=None):
        guard = " or ".join(f"'{u}' in _failed" for u in uses) or "False"
        out.append(f'_mark("op", "{sid}")')
        out.append("_TICKS[0] = 0")
        out.append("LOG.clear()")
        out.append(f"if {guard}:")
        out.append(f"    print('skip', '{sid}')")
        if defines:
            out.append(f"    _failed.add('{defines}')")
        out.append("else:")
        out.append("    try:")
        out.extend(f"        {l}" for l in lines)
        out.append("    except Exception as _e:")
        out.append("        _exc(_e)")
        if defines:
            out.append(f"        _failed.add('{defines}')")
        out.append(f'_mark("done", "{sid}")')
    for c in tree["classes"]:
        body = []
        for m in c["methods"]:
            body += method_lines(c["name"], m["name"], m["kind"], m["behaviour"])
        body += ["    def __repr__(self):", f"        return '{c['name']}'"]
        if c["fails"]:
            body += ["    hook = _Hook()"]
        base = "" if c["base"] == "object" else f"({c['base']})"
        lines = [f"class {c['name']}{base}:"] + body + ["r = None", "show(r)"]
        generated = [c["base"]] if c["base"] not in BASES else []
        step(f"c:{c['name']}", lines, generated, c["name"])
    for v in tree["values"]:
        if v["name"] == "SHARED":
            step("v:SHARED", ["show(len(SHARED))"], [], "SHARED")
            continue
        step(f"v:{v['name']}", [f"{v['name']} = {v['expr']}", f"SHARED.append({v['name']})",
                                f"show({v['name']})"], v["uses"], v["name"])
    for o in tree["ops"]:
        step(o["step"], [f"r = {o['expr']}", "show(r)"], o["uses"])
    if tree["seed_step"]:
        step("seed", ["r = list({'s1', 's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9'})", "show(r)"], [])
    return "\n".join(out) + "\n"


def digest(outdir):
    import hashlib
    h = hashlib.sha256()
    h.update(b"3.12\n")
    h.update(grid.TRACE_PY.read_bytes())
    for f in sorted(pathlib.Path(outdir).glob("fuzz_*.py")):
        h.update(f.name.encode() + b"\n")
        h.update(f.read_bytes())
    print(h.hexdigest())


def main():
    if len(sys.argv) == 3 and sys.argv[1] == "--digest":
        digest(sys.argv[2])
        return
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("outdir")
    ap.add_argument("--seed", default="1")
    ap.add_argument("--count", type=int, default=200)
    args = ap.parse_args()
    out = pathlib.Path(args.outdir)
    out.mkdir(parents=True, exist_ok=True)
    for old in list(out.glob("fuzz_*.py")) + list(out.glob("fuzz_*.json")):
        old.unlink()
    for i in range(args.count):
        tree = make(args.seed, i)
        (out / f"{tree['id']}.py").write_text(render(tree))
        (out / f"{tree['id']}.json").write_text(json.dumps(tree, indent=1))
        steps = [f"c:{c['name']}" for c in tree["classes"]] + [f"v:{v['name']}" for v in tree["values"]] + \
            [o["step"] for o in tree["ops"]] + (["seed"] if tree["seed_step"] else [])
        fails = [f"c:{c['name']}" for c in tree["classes"] if c["fails"]]
        print(f"{tree['id']} | {'seed' if tree['seed_step'] else 'plain'} | {','.join(steps)} | "
              f"{','.join(fails) or '-'}")


if __name__ == "__main__":
    main()
