"""The catalog of the axis grid: the kinds of input and the operations, as data.

`grid.py` turns the catalog into one program per case. A case is one operation (a template with
holes) with one kind of input on one axis, everything else plain. Each case has an expected
outcome: `result`, `raises:<ExcType>`, `rejects:<construct>` for a case that the translator
rejects on purpose, or `any` where the outcome isn't predicted (a dunder that returns a wrong
kind, some re-entry); for `any` the run is still checked to reach the operation. The axes:

* A1, the operand: an exact built-in value, an instance of a subclass (plain, with `__slots__`,
  with attributes, overriding the dunder that the operation looks up, or overriding another
  one), a user object that implements the protocol, one that doesn't, and `True` for an `int`.
* A2, re-entry: user code that changes the container or iterator that called it.
* A3, the descriptor kind of a special method: function, lambda, staticmethod, classmethod,
  property, callable object, a built-in method or function, `None`, an attribute of the
  instance, an inherited or second-base method, `__getattr__`.
* A4, failing user methods: they raise, or return the wrong kind of value.
* A5, values at the limits; A6, faults in iteration; A7, attributes of built-in objects; A8,
  binding errors of built-in methods.

Every user class of a case that prints its instances defines `__repr__`, and `grid.py` gives
every user dunder but `__repr__` and `__init__` an `ev(name)` call as its first line, so the number
and order of user calls is part of the output.
"""

from dataclasses import dataclass, field

# ---------------------------------------------------------------------------------------------
# Cases


@dataclass
class Case:
    """One grid case: the classes it defines, the statements that make its values, the
    statements of its operation (which assign `r`), and what CPython must do."""
    id: str
    group: str
    axis: str
    kind: str
    # The operation's name, e.g. `len` or `dict.get` (the template that `grid.py` prints is the
    # hash of `op`, not this name).
    operation: str
    op: list
    classes: list = field(default_factory=list)
    setup: list = field(default_factory=list)
    expect: str = "result"
    ident: str = ""
    entries: list = field(default_factory=list)
    receiver: str = ""


# ---------------------------------------------------------------------------------------------
# Built-in types and their values

# The subclassable built-in types of the model, and the exact value of each that a hole gets.
SUBCLASSABLE = {
    "int": "3",
    "float": "1.5",
    "str": "'ab'",
    "bytes": "b'ab'",
    "tuple": "(1, 2)",
    "list": "[1, 2]",
    "dict": "{'a': 1, 'b': 2}",
    "set": "{1, 2}",
    "frozenset": "frozenset({1, 2})",
}
# Final types: they get only the kinds `exact`, `user` and `user-not`.
FINAL = {"bool": "True", "range": "range(3)"}
EXACT = {**SUBCLASSABLE, **FINAL}

# Types whose instances may hold attributes when subclassed with `__slots__ = ('tag',)`;
# the others take only `__slots__ = ()`.
SLOTS_OK = {"list", "dict", "set", "frozenset", "float"}


def cls_name(base, suffix):
    return f"{base.capitalize()}{suffix}"


def repr_line(name):
    return f"    def __repr__(self):\n        return '{name}()'\n"


def subclass(base, suffix, body=""):
    """A subclass of `base`, with a `__repr__` that shows the built-in part too."""
    name = cls_name(base, suffix)
    rep = (f"    def __repr__(self):\n"
           f"        return '{name}(' + {base}.__repr__(self) + ')'\n")
    return name, f"class {name}({base}):\n{body}{rep}"


def method(name, params, body_lines, cls):
    """A user method that records its call, then runs `body_lines`."""
    lines = [f"    def {name}({params}):", f"        ev('{cls}.{name}')"]
    lines += [f"        {l}" for l in body_lines]
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------------------------
# Operations

@dataclass
class Op:
    """An operation template. `expr` uses `{x}` for the operand on the axis (and `{y}` for the
    second operand of a binary operation). `dunder` is the special method it looks up on `{x}`'s
    type, `over` the value the overriding dunder returns, `user` the body of a user class that
    implements the protocol, and `types` the built-in types it applies to, with the second
    operand for each (`None` for a unary operation). `stmt` makes `expr` a statement that
    assigns `r`. `raises` maps a (type, kind) to an expected exception where CPython raises
    although the operation applies."""
    name: str
    expr: str
    dunder: str
    over: str
    user: list
    types: dict
    group: str
    stmt: bool = False
    raises: dict = field(default_factory=dict)
    params: str = "self, *a"
    entry: str = ""
    lits: dict = field(default_factory=dict)


def bin_op(name, sym, dunder, types, raises=None, lits=None):
    return Op(name, "{x} " + sym + " {y}", dunder, "'over'",
              ["return 'user'"], types, "operators", raises=raises or {},
              params="self, other", entry=dunder, lits=lits or {})


NUM = {"int": "2", "float": "2.0", "bool": "True"}
SEQ_ADD = {"str": "'c'", "bytes": "b'c'", "tuple": "(3,)", "list": "[3]"}
SEQ_MUL = {"str": "2", "bytes": "2", "tuple": "2", "list": "2"}
SETS = {"set": "{2, 3}", "frozenset": "frozenset({2, 3})"}

OPERATIONS = [
    bin_op("add", "+", "__add__", {**NUM, **SEQ_ADD}),
    bin_op("sub", "-", "__sub__", {**NUM, **SETS}),
    bin_op("mul", "*", "__mul__", {**NUM, **SEQ_MUL}),
    bin_op("truediv", "/", "__truediv__", NUM),
    bin_op("floordiv", "//", "__floordiv__", NUM),
    bin_op("mod", "%", "__mod__", {**NUM, "str": "(1, 2)", "bytes": "(1,)"},
           lits={"str": "'a%sb%s'", "bytes": "b'a%db'"},
           # `str.__mod__` takes any right operand, so a user `__rmod__` is never asked.
           raises={("str", "exact/user"): "TypeError", ("str", "sub/user"): "TypeError"}),
    bin_op("pow", "**", "__pow__", NUM),
    bin_op("lshift", "<<", "__lshift__", {"int": "2", "bool": "True"}),
    bin_op("rshift", ">>", "__rshift__", {"int": "1", "bool": "True"}),
    bin_op("and", "&", "__and__", {"int": "2", "bool": "True", **SETS}),
    bin_op("or", "|", "__or__", {"int": "2", "bool": "True", **SETS, "dict": "{'c': 3}"}),
    bin_op("xor", "^", "__xor__", {"int": "2", "bool": "True", **SETS}),
    bin_op("eq", "==", "__eq__", {t: EXACT[t] for t in EXACT}),
    bin_op("ne", "!=", "__ne__", {t: EXACT[t] for t in EXACT}),
    bin_op("lt", "<", "__lt__", {**NUM, "str": "'b'", "bytes": "b'b'", "tuple": "(1, 3)",
                                 "list": "[1, 3]", **SETS}),
    bin_op("ge", ">=", "__ge__", {**NUM, "str": "'b'", "tuple": "(1, 3)", "list": "[1, 3]",
                                  **SETS}),
    Op("neg", "-{x}", "__neg__", "'over'", ["return 'user'"], {"int": None, "float": None,
       "bool": None}, "operators", entry="__neg__"),
    Op("invert", "~{x}", "__invert__", "'over'", ["return 'user'"], {"int": None},
       "operators", entry="__invert__"),
    Op("not", "not {x}", "__bool__", "False", ["return False"],
       {t: None for t in EXACT}, "operators", entry="__bool__"),
    Op("truthy", "1 if {x} else 0", "__bool__", "False", ["return False"],
       {t: None for t in EXACT}, "operators", entry="__bool__"),
    Op("iadd", "r = {x}\nr += {y}", "__iadd__", "'over'", ["return 'user'"],
       {"list": "[3]", "int": "2", "str": "'c'", "tuple": "(3,)"}, "operators", stmt=True,
       params="self, other", entry="__iadd__"),
    Op("ior", "r = {x}\nr |= {y}", "__ior__", "'over'", ["return 'user'"],
       {"set": "{3}", "dict": "{'c': 3}", "int": "4"}, "operators", stmt=True,
       params="self, other", entry="__ior__"),
    Op("in", "1 in {x}", "__contains__", "True", ["return True"],
       {"tuple": None, "list": None, "dict": None, "set": None, "frozenset": None,
        "range": None}, "containers", entry="__contains__"),
    Op("str_in", "'a' in {x}", "__contains__", "True", ["return True"], {"str": None},
       "containers", entry="__contains__"),
    Op("getitem", "{x}[0]", "__getitem__", "'over'", ["return 'user'"],
       {"str": None, "bytes": None, "tuple": None, "list": None, "range": None},
       "containers", entry="__getitem__"),
    Op("getkey", "{x}['a']", "__getitem__", "'over'", ["return 'user'"], {"dict": None},
       "containers", entry="__getitem__"),
    Op("slice", "{x}[0:1]", "__getitem__", "'over'", ["return 'user'"],
       {"str": None, "bytes": None, "tuple": None, "list": None, "range": None},
       "containers", entry="__getitem__"),
    Op("setitem", "r = {x}\nr[0] = 9", "__setitem__", "None", ["return None"],
       {"list": None, "dict": None}, "containers", stmt=True, entry="__setitem__"),
    Op("delitem", "r = {x}\ndel r[0]", "__delitem__", "None", ["return None"],
       {"list": None}, "containers", stmt=True, entry="__delitem__"),
    Op("unpack", "a, b = {x}\nr = (a, b)", "__iter__", "iter([7, 8])", ["return iter([5, 6])"],
       {"tuple": None, "list": None, "str": None, "bytes": None, "dict": None, "set": None,
        "frozenset": None}, "containers", stmt=True, entry="__iter__"),
    Op("unpack_ex", "a, *b = {x}\nr = (a, b)", "__iter__", "iter([7, 8])",
       ["return iter([5, 6])"], {"tuple": None, "list": None, "str": None, "range": None},
       "containers", stmt=True, entry="__iter__"),
    Op("star_list", "[*{x}]", "__iter__", "iter([7])", ["return iter([5])"],
       {"tuple": None, "list": None, "str": None, "dict": None, "set": None, "range": None},
       "containers", entry="__iter__"),
    Op("star_set", "sorted({*{x}})", "__iter__", "iter([7])", ["return iter([5])"],
       {"tuple": None, "list": None, "set": None, "frozenset": None}, "containers",
       entry="__iter__"),
    Op("star_args", "(lambda *a: a)(*{x})", "__iter__", "iter([7])", ["return iter([5])"],
       {"tuple": None, "list": None, "str": None}, "containers", entry="__iter__"),
    Op("star_kwargs", "(lambda **k: sorted(k.items()))(**{x})", "keys", "['a']",
       ["return ['k']"], {"dict": None}, "containers", entry="keys"),
    Op("dict_display", "{**{x}}", "keys", "['a']", ["return ['k']"], {"dict": None},
       "containers", entry="keys"),
    Op("for", "r = []\nfor v in {x}:\n    r.append(v)", "__iter__", "iter([7])",
       ["return iter([5])"], {"tuple": None, "list": None, "str": None, "dict": None,
                              "range": None}, "containers", stmt=True, entry="__iter__"),
    Op("listcomp", "[v for v in {x}]", "__iter__", "iter([7])", ["return iter([5])"],
       {"tuple": None, "list": None, "str": None, "set": None}, "containers",
       entry="__iter__"),
    Op("len", "len({x})", "__len__", "7", ["return 4"],
       {t: None for t in ["str", "bytes", "tuple", "list", "dict", "set", "frozenset",
                          "range"]}, "builtins", entry="__len__"),
    Op("repr", "repr({x})", "__repr__", "'over'", ["return 'user'"],
       {t: None for t in EXACT}, "builtins", entry="__repr__"),
    Op("str", "str({x})", "__str__", "'over'", ["return 'user'"],
       {t: None for t in EXACT}, "builtins", entry="__str__"),
    Op("format", "format({x}, '')", "__format__", "'over'", ["return 'user'"],
       {t: None for t in ["int", "float", "str", "bool"]}, "builtins",
       params="self, spec", entry="__format__"),
    Op("fstring", "f'<{{x}}>'", "__format__", "'over'", ["return 'user'"],
       {t: None for t in ["int", "float", "str"]}, "builtins", params="self, spec",
       entry="__format__"),
    Op("hash", "hash({x}) if type({x}).__hash__ is not object.__hash__ else 'by address'", "__hash__", "5", ["return 6"],
       {t: None for t in ["int", "float", "tuple", "frozenset", "bool"]}, "builtins",
       params="self", entry="__hash__"),
    Op("int", "int({x})", "__int__", "8", ["return 9"], {"int": None, "float": None,
       "bool": None}, "builtins", params="self", entry="__int__"),
    Op("float", "float({x})", "__float__", "8.5", ["return 9.5"], {"int": None,
       "float": None}, "builtins", params="self", entry="__float__"),
    Op("index", "[10, 20, 30, 40][{x}]", "__index__", "2", ["return 1"],
       {"int": None, "bool": None}, "builtins", params="self", entry="__index__"),
    Op("abs", "abs({x})", "__abs__", "'over'", ["return 'user'"], {"int": None,
       "float": None}, "builtins", params="self", entry="__abs__"),
    Op("bool", "bool({x})", "__bool__", "False", ["return False"],
       {t: None for t in EXACT}, "builtins", params="self", entry="__bool__"),
    Op("iter_next", "next(iter({x}))", "__iter__", "iter([7])", ["return iter([5])"],
       {"str": None, "tuple": None, "list": None, "dict": None, "range": None},
       "builtins", params="self", entry="__iter__"),
    Op("list_of", "list({x})", "__iter__", "iter([7])", ["return iter([5])"],
       {"str": None, "tuple": None, "list": None, "dict": None, "range": None,
        "set": None}, "builtins", params="self", entry="__iter__"),
    Op("tuple_of", "tuple({x})", "__iter__", "iter([7])", ["return iter([5])"],
       {"str": None, "list": None, "range": None}, "builtins", params="self",
       entry="__iter__"),
    Op("sorted", "sorted({x})", "__iter__", "iter([7, 6])", ["return iter([5, 4])"],
       {"str": None, "tuple": None, "list": None, "set": None, "frozenset": None},
       "builtins", params="self", entry="__iter__"),
    Op("sum", "sum({x})", "__iter__", "iter([7, 6])", ["return iter([5, 4])"],
       {"tuple": None, "list": None, "set": None, "range": None}, "builtins",
       params="self", entry="__iter__"),
    Op("max", "max({x})", "__iter__", "iter([7, 6])", ["return iter([5, 4])"],
       {"str": None, "tuple": None, "list": None, "range": None}, "builtins",
       params="self", entry="__iter__"),
    Op("any", "any({x})", "__iter__", "iter([0])", ["return iter([0])"],
       {"tuple": None, "list": None, "str": None}, "builtins", params="self",
       entry="__iter__"),
    Op("dict_of", "dict({x})", "keys", "['a']", ["return ['k']"], {"dict": None},
       "builtins", params="self", entry="keys"),
    Op("set_of", "sorted(set({x}))", "__iter__", "iter([7])", ["return iter([5])"],
       {"tuple": None, "list": None, "set": None, "frozenset": None}, "builtins",
       params="self", entry="__iter__"),
    Op("join", "'-'.join({x})", "__iter__", "iter(['q'])", ["return iter(['u'])"],
       {"str": None}, "builtins", params="self", entry="__iter__"),
    Op("isinstance", "isinstance({x}, int)", "__class__", "", [], {t: None for t in EXACT},
       "builtins"),
    Op("print", "print({x})", "__str__", "'over'", ["return 'user'"],
       {t: None for t in EXACT}, "builtins", params="self", entry="__str__"),
]

# The user objects that implement `keys` also need `__getitem__` for the mapping protocol.
MAPPING_USER_EXTRA = {"keys": [("__getitem__", "self, k", ["return 0"])]}


# ---------------------------------------------------------------------------------------------
# A1: operand kinds


def a1_kinds(base):
    """The A1 kinds that apply to a hole of the built-in type `base`."""
    kinds = ["exact"]
    if base in SUBCLASSABLE:
        kinds += ["sub", "sub-slots", "sub-dict", "sub-over", "sub-over-other"]
    if base == "int":
        kinds += ["bool-as-int"]
    kinds += ["user", "user-not"]
    return kinds


OTHER_DUNDER = {"__iter__": ("__len__", "self", ["return 99"]),
                "keys": ("__iter__", "self", ["return iter(['zz'])"])}


def a1_value(op, base, kind, side, var):
    """The classes and setup lines of the value of kind `kind` for a hole of type `base`, bound
    to `var`; `side` is 'l' or 'r' (a binary operation's right operand overrides the reflected
    dunder)."""
    lit = op.lits.get(base, EXACT[base]) if side == "l" else EXACT[base]
    dunder = op.dunder
    if side == "r" and dunder.startswith("__") and op.group == "operators" and op.params == "self, other":
        dunder = reflected(dunder)
    sfx = side.upper()
    if kind == "exact":
        return [], [f"{var} = {lit}"]
    if kind == "bool-as-int":
        return [], [f"{var} = True"]
    if kind == "sub":
        n, c = subclass(base, "S" + sfx)
        return [c], [f"{var} = {n}({lit})"]
    if kind == "sub-slots":
        slots = "('tag',)" if base in SLOTS_OK else "()"
        n, c = subclass(base, "Sl" + sfx, f"    __slots__ = {slots}\n")
        return [c], [f"{var} = {n}({lit})"]
    if kind == "sub-dict":
        n, c = subclass(base, "Sd" + sfx)
        return [c], [f"{var} = {n}({lit})", f"{var}.tag = 1"]
    if kind == "sub-over":
        n = cls_name(base, "So" + sfx)
        body = method(dunder, op.params, [f"return {op.over}"], n)
        _, c = subclass(base, "So" + sfx, body)
        return [c], [f"{var} = {n}({lit})"]
    if kind == "sub-over-other":
        oname, oparams, obody = OTHER_DUNDER.get(op.dunder, ("__iter__", "self",
                                                             ["return iter([77])"]))
        n = cls_name(base, "Soo" + sfx)
        body = method(oname, oparams, obody, n)
        _, c = subclass(base, "Soo" + sfx, body)
        return [c], [f"{var} = {n}({lit})"]
    if kind == "user":
        n = "User" + sfx
        body = method(dunder, op.params, op.user, n)
        for (d, p, b) in MAPPING_USER_EXTRA.get(op.dunder, []):
            body += method(d, p, b, n)
        return [f"class {n}:\n{body}{repr_line(n)}"], [f"{var} = {n}()"]
    if kind == "user-not":
        n = "Plain" + sfx
        return [f"class {n}:\n{repr_line(n)}"], [f"{var} = {n}()"]
    raise ValueError(kind)


REFLECTED = {"__add__": "__radd__", "__sub__": "__rsub__", "__mul__": "__rmul__",
             "__truediv__": "__rtruediv__", "__floordiv__": "__rfloordiv__",
             "__mod__": "__rmod__", "__pow__": "__rpow__", "__lshift__": "__rlshift__",
             "__rshift__": "__rrshift__", "__and__": "__rand__", "__or__": "__ror__",
             "__xor__": "__rxor__", "__eq__": "__eq__", "__ne__": "__ne__",
             "__lt__": "__gt__", "__ge__": "__le__", "__iadd__": "__radd__",
             "__ior__": "__ror__"}


def reflected(d):
    return REFLECTED.get(d, d)


def a1_expect(op, base, kind, other_kind="exact"):
    """The outcome CPython gives for A1 kind `kind` (and `other_kind` on a binary operation's
    other side)."""
    for key in ((base, kind), (base, f"{kind}/{other_kind}")):
        if key in op.raises:
            return "raises:" + op.raises[key]
    kinds = {kind, other_kind}
    if op.name in ("isinstance", "print", "repr", "str", "eq", "ne", "not", "truthy", "bool",
                   "hash", "format", "fstring") and "user-not" in kinds:
        return "result"
    if "user-not" in kinds and "user" not in kinds and not (
            op.group == "operators" and op.params == "self, other"
            and "sub-over" in kinds):
        return "raises:TypeError"
    return "result"


def a1_cases():
    cases = []
    for op in OPERATIONS:
        binary = "{y}" in op.expr
        for base, other in op.types.items():
            pairs = binary and base in ("int", "str", "set")
            lkinds = a1_kinds(base)
            if base not in SUBCLASSABLE and op.name not in ("isinstance",):
                lkinds = [k for k in lkinds if not k.startswith("sub")]
            combos = [(k, "exact") for k in lkinds]
            if pairs:
                # The right operand gets the kinds of its own type.
                rbase = type_of_literal(other) if other is not None else base
                rkinds = a1_kinds(rbase)
                combos = [(lk, rk) for lk in lkinds for rk in rkinds
                          if lk in ("exact", "sub", "sub-over", "user", "user-not")
                          and rk in ("exact", "sub", "sub-over", "user", "user-not")]
                combos += [(k, "exact") for k in lkinds if k not in
                           ("exact", "sub", "sub-over", "user", "user-not")]
            for lk, rk in combos:
                if op.name == "isinstance" and lk in ("user", "sub-over", "sub-over-other"):
                    continue
                cid = f"a1_{op.name}_{base}_{lk}" + (f"_{rk}" if binary and pairs else "")
                classes, setup = a1_value(op, base, lk, "l", "x")
                expr = op.expr
                if binary:
                    rbase = type_of_literal(other)
                    if pairs:
                        c2, s2 = a1_value(op, rbase, rk, "r", "y")
                    else:
                        c2, s2 = [], [f"y = {other}"]
                    classes += c2
                    setup += s2
                code = expr.replace("{x}", "x").replace("{y}", "y")
                lines = code.split("\n") if op.stmt else [f"r = {code}"]
                ident = "x" if lk.startswith("sub") and op.name in IDENTITY_OPS else ""
                cases.append(Case(cid, op.group, "A1", lk if not pairs else f"{lk}/{rk}",
                                  op.name, lines, classes, setup,
                                  a1_expect(op, base, lk, rk), ident,
                                  [(base, op.entry)] if op.entry and lk in ("exact", "sub")
                                  else []))
    return cases


# Operations that may return their own operand; the case prints `r is x` for a subclass operand.
IDENTITY_OPS = {"str", "format", "fstring", "add", "mul", "mod", "iadd", "ior"}


def type_of_literal(lit):
    for t, v in EXACT.items():
        if v == lit:
            return t
    if lit.startswith("'"):
        return "str"
    if lit.startswith("b'"):
        return "bytes"
    if lit.startswith("frozenset"):
        return "frozenset"
    if lit.startswith("{'") or lit == "{}":
        return "dict"
    if lit.startswith("{"):
        return "set"
    if lit.startswith("("):
        return "tuple"
    if lit.startswith("["):
        return "list"
    if lit in ("True", "False"):
        return "bool"
    if "." in lit:
        return "float"
    return "int"


# ---------------------------------------------------------------------------------------------
# A3: descriptor kinds at special-method lookup sites

# (dunder, how the case uses it, the value the dunder returns, its parameters, whether
# `object` has a default for it).
SITES = [
    ("__len__", "len(x)", "3", "self", False),
    ("__iter__", "list(x)", "iter([1, 2])", "self", False),
    ("__contains__", "1 in x", "True", "self, v", False),
    ("__getitem__", "x[0]", "7", "self, k", False),
    ("__setitem__", "x[0] = 1", "None", "self, k, v", False),
    ("__delitem__", "del x[0]", "None", "self, k", False),
    ("__bool__", "bool(x)", "False", "self", True),
    ("__index__", "[10, 20, 30][x]", "2", "self", False),
    ("__hash__", "hash(x)", "5", "self", True),
    ("__eq__", "x == 1", "True", "self, o", True),
    ("__lt__", "x < 1", "True", "self, o", False),
    ("__add__", "x + 1", "'add'", "self, o", False),
    ("__radd__", "1 + x", "'radd'", "self, o", False),
    ("__iadd__", "x += 1", "'iadd'", "self, o", False),
    ("__neg__", "-x", "'neg'", "self", False),
    ("__str__", "str(x)", "'S'", "self", True),
    ("__repr__", "repr(x)", "'R'", "self", True),
    ("__format__", "format(x, '')", "'F'", "self, s", True),
    ("__call__", "x()", "'called'", "self", False),
    ("__int__", "int(x)", "4", "self", False),
    ("__float__", "float(x)", "4.5", "self", False),
    ("__next__", "next(x)", "1", "self", False),
    ("__reversed__", "list(reversed(x))", "iter([3])", "self", False),
    ("__length_hint__", "list(x)", "2", "self", False),
    ("__abs__", "abs(x)", "'abs'", "self", False),
    ("__getattr__", "x.missing", "'ga'", "self, n", False),
]

# Dunders whose `object` default depends on the object's address.
ADDRESS_DEFAULTS = {"__hash__", "__repr__", "__format__"}

A3_KINDS = ["function", "lambda", "staticmethod", "classmethod", "property", "callable",
            "none", "instance", "inherited", "second-base", "getattr", "getattribute",
            "metaclass", "builtin-method", "builtin-function"]

# For each site, a built-in method of another type with the same name (a method or wrapper
# descriptor that requires that type's `self`), and a built-in function to set it to.
BUILTIN_OTHER = {
    "__len__": "list.__len__", "__iter__": "list.__iter__", "__contains__": "list.__contains__",
    "__getitem__": "list.__getitem__", "__setitem__": "list.__setitem__",
    "__delitem__": "list.__delitem__", "__bool__": "int.__bool__", "__index__": "int.__index__",
    "__hash__": "int.__hash__", "__eq__": "int.__eq__", "__lt__": "int.__lt__",
    "__add__": "int.__add__", "__radd__": "int.__radd__", "__iadd__": "list.__iadd__",
    "__neg__": "int.__neg__", "__str__": "int.__repr__", "__repr__": "str.upper",
    "__format__": "int.__format__", "__call__": "type.__call__", "__int__": "float.__int__",
    "__float__": "int.__float__", "__next__": "list.__len__",
    "__reversed__": "list.__reversed__", "__length_hint__": "list.__len__",
    "__abs__": "int.__abs__", "__getattr__": "str.upper",
}
BUILTIN_FUNCTION = {
    "__len__": "len", "__iter__": "iter", "__contains__": "callable", "__getitem__": "repr",
    "__setitem__": "print", "__delitem__": "callable", "__bool__": "callable",
    "__index__": "len", "__hash__": "id", "__eq__": "isinstance", "__lt__": "isinstance",
    "__add__": "isinstance", "__radd__": "isinstance", "__iadd__": "isinstance",
    "__neg__": "abs", "__str__": "repr", "__repr__": "str", "__format__": "format",
    "__call__": "print", "__int__": "hash", "__float__": "hash", "__next__": "iter",
    "__reversed__": "iter", "__length_hint__": "len", "__abs__": "abs", "__getattr__": "len",
}


def a3_case(dunder, use, ret, params, has_default, kind):
    cid = f"a3_{dunder.strip('_')}_{kind}"
    classes = []
    ev_ = f"ev('C.{dunder}')"
    body = {
        "function": f"    def {dunder}({params}):\n        {ev_}\n        return {ret}\n",
        "lambda": f"    {dunder} = lambda self, *a: ({ev_}, {ret})[1]\n",
        "staticmethod": f"    @staticmethod\n    def {dunder}(*a):\n        {ev_}\n        return {ret}\n",
        "classmethod": f"    @classmethod\n    def {dunder}(cls, *a):\n        {ev_}\n        return {ret}\n",
        "property": f"    @property\n    def {dunder}(self):\n        {ev_}\n        return lambda *a: {ret}\n",
        "callable": f"    {dunder} = Call()\n",
        "none": f"    {dunder} = None\n",
        "instance": "",
        "inherited": "",
        "second-base": "",
        "getattribute": (f"    def __getattribute__(self, n):\n        ev('C.__getattribute__')\n        return lambda *a: {ret}\n"),
        "metaclass": "",
        "builtin-method": f"    {dunder} = {BUILTIN_OTHER[dunder]}\n",
        "builtin-function": f"    {dunder} = {BUILTIN_FUNCTION[dunder]}\n",
        "getattr": (f"    def __getattr__(self, n):\n        ev('C.__getattr__')\n        return {ret}\n"
                    if dunder == "__getattr__" else
                    f"    def __getattr__(self, n):\n        ev('C.__getattr__')\n        return lambda *a: {ret}\n"),
    }[kind]
    if kind == "callable":
        classes.append(f"class Call:\n    def __call__(self, *a):\n        {ev_}\n        return {ret}\n{repr_line('Call')}")
    bases = ""
    if kind == "inherited":
        classes.append(f"class Base:\n    def {dunder}({params}):\n        {ev_}\n        return {ret}\n{repr_line('Base')}")
        bases = "(Base)"
    meta = ""
    if kind == "metaclass":
        # Found on the metaclass, so not in the MRO of the instance's type.
        classes.append(f"class M(type):\n    def {dunder}({params}):\n        {ev_}\n        return {ret}\n")
        meta = "(metaclass=M)"
    if kind == "second-base":
        classes.append(f"class First:\n    pass\n")
        classes.append(f"class Second:\n    def {dunder}({params}):\n        {ev_}\n        return {ret}\n{repr_line('Second')}")
        bases = "(First, Second)"
    rep = "" if dunder == "__repr__" else repr_line("C")
    extra = ""
    if dunder == "__length_hint__":
        extra = "    def __iter__(self):\n        return iter([1, 2])\n"
    head = f"class C{bases[:-1] + ', metaclass=M)' if bases and meta else bases or meta}:\n"
    classes.append(head + (body + extra + rep if (body or extra or rep) else "    pass\n"))
    setup = ["x = C()"]
    if kind == "instance":
        setup.append(f"x.{dunder} = lambda *a: (ev('x.{dunder}'), {ret})[1]")
    if " = " in use or "+=" in use or use.startswith("del "):
        op = [use, "r = x"]
    elif kind in ("instance", "getattr", "getattribute", "metaclass") and dunder in ADDRESS_DEFAULTS:
        # `object`'s default depends on the address; only its type is observed.
        op = [f"r = type({use}).__name__"]
    else:
        op = [f"r = {use}"]
    callable_kinds = {"function", "lambda", "staticmethod", "classmethod", "property",
                      "callable", "inherited", "second-base"}
    if dunder == "__getattr__":
        callable_kinds |= {"getattr", "getattribute"}
    if kind in ("builtin-method", "builtin-function"):
        expect = "any"
    elif dunder == "__length_hint__":
        expect = "result"
    elif kind in callable_kinds:
        expect = "result"
    elif kind in ("instance", "getattr", "getattribute", "metaclass") and has_default:
        expect = "result"
    elif kind == "none" and dunder == "__getattr__":
        expect = "raises:TypeError"
    elif dunder == "__getattr__":
        expect = "raises:AttributeError"
    else:
        expect = "raises:TypeError"
    return Case(cid, "lookup", "A3", kind, dunder, op, classes, setup, expect)


# Cases left out: CPython's `trace.py` compares the program's globals with `in`, which calls a
# metaclass's `__eq__` on the class `C` while it renders them, so that case's trace shows calls
# that no operation made.
A3_LEFT_OUT = {("__eq__", "metaclass")}


def a3_cases():
    return [a3_case(*site, kind) for site in SITES for kind in A3_KINDS
            if (site[0], kind) not in A3_LEFT_OUT]


# ---------------------------------------------------------------------------------------------
# A4: failing user methods

A4_KINDS = {
    "raise-value": ("raise ValueError('boom')", "raises:ValueError"),
    "raise-user": ("raise Oops('boom')", "raises:Oops"),
    "raise-stop": ("raise StopIteration", None),
    "raise-key": ("raise KeyError('k')", "raises:KeyError"),
    "wrong-str": ("return 'wrong'", None),
    "wrong-none": ("return None", None),
    "wrong-neg": ("return -1", None),
    "wrong-big": ("return 2 ** 70", None),
    "sub-result": ("return Isub(1)", None),
    "not-impl": ("return NotImplemented", None),
}


def a4_cases():
    cases = []
    for dunder, use, ret, params, has_default in SITES:
        if dunder in ("__getattr__",):
            continue
        for kind, (stmt, expect) in A4_KINDS.items():
            cid = f"a4_{dunder.strip('_')}_{kind}"
            extra = ""
            if dunder == "__length_hint__":
                extra = "    def __iter__(self):\n        return iter([1, 2])\n"
            classes = ["class Oops(Exception):\n    pass\n", "class Isub(int):\n    pass\n"]
            body = f"    def {dunder}({params}):\n        ev('C.{dunder}')\n        {stmt}\n"
            rep = "" if dunder == "__repr__" else repr_line("C")
            classes.append(f"class C:\n{body}{extra}{rep}")
            if " = " in use or "+=" in use or use.startswith("del"):
                op = [use, "r = 0"]
            else:
                op = [f"r = {use}"]
            cases.append(Case(cid, "failing", "A4", kind, dunder, op, classes, ["x = C()"],
                              expect or "any"))
    return cases


# ---------------------------------------------------------------------------------------------
# A2: re-entry, A5: limits, A6: iteration faults (hand-written templates)

A2 = {
    "sort_key_append": (["xs = [3, 1, 2]",
                         "def k(v):\n    ev('k')\n    xs.append(0)\n    return v"],
                        ["xs.sort(key=k)", "r = xs"], "raises:ValueError"),
    "sort_lt_clear": (["class N:\n    def __init__(self, v):\n        self.v = v\n    def __lt__(self, o):\n        ev('N.__lt__')\n        xs.clear()\n        return self.v < o.v\n    def __repr__(self):\n        return 'N(%d)' % self.v\n",
                       "xs = [N(3), N(1), N(2)]"], ["xs.sort()", "r = xs"], "any"),
    "list_eq_clear_remove": (["class E:\n    def __eq__(self, o):\n        ev('E.__eq__')\n        xs.clear()\n        return False\n    def __repr__(self):\n        return 'E()'\n",
                              "xs = [E(), E(), 5]"], ["xs.remove(5)", "r = xs"], "any"),
    "list_eq_clear_index": (["class E:\n    def __eq__(self, o):\n        ev('E.__eq__')\n        xs.clear()\n        return False\n    def __repr__(self):\n        return 'E()'\n",
                             "xs = [E(), E(), 5]"], ["r = xs.index(5)"], "any"),
    "list_eq_clear_in": (["class E:\n    def __eq__(self, o):\n        ev('E.__eq__')\n        xs.clear()\n        return False\n    def __repr__(self):\n        return 'E()'\n",
                          "xs = [E(), E(), 5]"], ["r = 5 in xs"], "any"),
    "extend_self_iter": (["xs = [1, 2]",
                          "class I:\n    def __iter__(self):\n        return self\n    def __next__(self):\n        ev('I.__next__')\n        if len(xs) > 6:\n            raise StopIteration\n        xs.append(len(xs))\n        return 0\n    def __repr__(self):\n        return 'I()'\n"],
                         ["xs.extend(I())", "r = xs"], "result"),
    "dict_iter_insert": (["d = {1: 1, 2: 2}"],
                         ["for k in d:\n    d[k + 10] = 0", "r = d"], "raises:RuntimeError"),
    "dict_iter_delete": (["d = {1: 1, 2: 2}"],
                         ["for k in d:\n    del d[k]", "r = d"], "raises:RuntimeError"),
    "set_iter_add": (["s = {1, 2}"], ["for k in s:\n    s.add(k + 10)", "r = s"],
                     "raises:RuntimeError"),
    "dict_eq_rebuild": (["class K:\n    done = False\n    def __init__(self, v):\n        self.v = v\n    def __hash__(self):\n        return 1\n    def __eq__(self, o):\n        ev('K.__eq__')\n        if not K.done:\n            K.done = True\n            d.clear()\n            d[K(9)] = 'new'\n        return False\n    def __repr__(self):\n        return 'K(%d)' % self.v\n",
                         "d = {}", "d[K(1)] = 'a'"], ["d[K(2)] = 'b'", "r = sorted([k.v for k in d])"],
                        "any"),
    "set_eq_clear": (["class K:\n    def __hash__(self):\n        return 1\n    def __eq__(self, o):\n        ev('K.__eq__')\n        s.clear()\n        return False\n    def __repr__(self):\n        return 'K()'\n",
                      "s = set()", "s.add(K())"], ["r = (K() in s, len(s))"], "any"),
    "iter_sentinel_exhaust": (["xs = [1, 2, 3]", "it = iter(xs)",
                               "def f():\n    ev('f')\n    return next(it)"],
                              ["r = list(iter(f, 3))"], "result"),
    "zip_advance": (["it = iter([1, 2, 3, 4])",
                     "class A:\n    def __iter__(self):\n        return self\n    def __next__(self):\n        ev('A.__next__')\n        return next(it)\n    def __repr__(self):\n        return 'A()'\n"],
                    ["r = list(zip(A(), it))"], "result"),
    "max_key_mutate": (["xs = [3, 1, 2]",
                        "def k(v):\n    ev('k')\n    if len(xs) < 5:\n        xs.append(9)\n    return v"],
                       ["r = (max(xs, key=k), len(xs))"], "result"),
    "join_mutate": (["xs = ['a', 'b']",
                     "class G:\n    def __iter__(self):\n        ev('G.__iter__')\n        xs.append('c')\n        return iter(xs)\n    def __repr__(self):\n        return 'G()'\n"],
                    ["r = '-'.join(G())"], "result"),
    "repr_self_list": (["l = [1]", "l.append(l)"], ["r = repr(l)"], "result"),
    "repr_self_dict": (["d = {}", "d[1] = d"], ["r = repr(d)"], "result"),
    "eq_self_list": (["l = [1]", "l.append(l)"], ["r = l == l"], "result"),
    "eq_mutual_lists": (["a = [1]", "b = [1]", "a.append(b)", "b.append(a)"], ["r = a == b"],
                        "raises:RecursionError"),
    "replace_eq_during_lookup": (["class K:\n    def __hash__(self):\n        return 1\n    def __eq__(self, o):\n        ev('K.__eq__')\n        K.__eq__ = lambda s, o: (ev('K.__eq__ (new)'), True)[1]\n        return False\n    def __repr__(self):\n        return 'K()'\n",
                                  "d = {K(): 1}"], ["r = (K() in d, K() in d)"], "any"),
    "dict_update_keys_mutate": (["class M:\n    def keys(self):\n        ev('M.keys')\n        return ['a', 'b']\n    def __getitem__(self, k):\n        ev('M.__getitem__')\n        d.clear()\n        return k\n    def __repr__(self):\n        return 'M()'\n",
                                 "d = {'z': 0}"], ["d.update(M())", "r = sorted(d.items())"], "result"),
}

A5 = {
    "int_str_limit": ([], ["r = len(str(10 ** 5000))"], "raises:ValueError"),
    "int_str_4300": ([], ["r = len(str(10 ** 4299))"], "result"),
    "index_huge": ([], ["r = [1][10 ** 20]"], "raises:IndexError"),
    "repeat_overflow": ([], ["r = 'ab' * 2 ** 62"], "raises:OverflowError"),
    "list_repeat_overflow": ([], ["r = [0] * 2 ** 62"], "any"),
    "len_huge": (["class B:\n    def __len__(self):\n        ev('B.__len__')\n        return 2 ** 70\n    def __repr__(self):\n        return 'B()'\n"],
                 ["r = len(B())"], "raises:OverflowError"),
    "hash_huge": (["class B:\n    def __hash__(self):\n        ev('B.__hash__')\n        return 2 ** 70\n    def __repr__(self):\n        return 'B()'\n"],
                  ["r = hash(B())"], "result"),
    "nan_eq": ([], ["n = float('nan')", "r = (n == n, [n] == [n], n in [n])"], "result"),
    "neg_zero": ([], ["r = (-0.0 == 0.0, repr(-0.0), hash(-0.0), round(2.5), round(-0.5))"],
                 "result"),
    "inf": ([], ["r = (float('inf') > 10 ** 400, repr(float('-inf')))"], "result"),
    "empty_max": ([], ["r = max([])"], "raises:ValueError"),
    "empty_unpack": ([], ["a, = []", "r = a"], "raises:ValueError"),
    "slice_neg_step": ([], ["r = ([1, 2, 3][::-1], 'abc'[::-2], (1, 2, 3)[5:1:-1])"],
                       "result"),
    "slice_zero_step": ([], ["r = [1, 2][::0]"], "raises:ValueError"),
    "nonbmp": ([], ["s = '\\U0001F600a'", "r = (len(s), s[0] == s, s.upper(), repr(s))"],
               "result"),
    "deep_list_repr": (["x = []", "for i in range(100):\n    x = [x]"], ["r = len(repr(x))"],
                       "result"),
    "deep_list_eq": (["x = []", "y = []", "for i in range(100):\n    x = [x]\n    y = [y]"],
                     ["r = x == y"], "result"),
    "big_int_ops": ([], ["v = 10 ** 300", "r = (v // 7 % 1000, -v // 3 % 10, (v + 1) % 9, v.__hash__() % 1000)"],
                    "result"),
    "str_sub_keyword": (["class K(str):\n    pass\n"],
                        ["r = (lambda **kw: sorted(kw))(**{K('a'): 1})"], "result"),
    "bool_index": ([], ["r = (['a', 'b'][True], True + True, (1, 2)[False])"], "result"),
}

A6 = {
    "iter_raises": (["class I:\n    def __iter__(self):\n        ev('I.__iter__')\n        raise ValueError('it')\n    def __repr__(self):\n        return 'I()'\n"],
                    ["r = list(I())"], "raises:ValueError"),
    "iter_not_iterator": (["class I:\n    def __iter__(self):\n        ev('I.__iter__')\n        return 5\n    def __repr__(self):\n        return 'I()'\n"],
                          ["r = list(I())"], "raises:TypeError"),
    "next_raises": (["class I:\n    def __iter__(self):\n        return self\n    def __next__(self):\n        ev('I.__next__')\n        raise KeyError('n')\n    def __repr__(self):\n        return 'I()'\n"],
                    ["r = [v for v in I()]"], "raises:KeyError"),
    "stop_with_value": (["class I:\n    def __iter__(self):\n        return self\n    def __next__(self):\n        ev('I.__next__')\n        raise StopIteration(5)\n    def __repr__(self):\n        return 'I()'\n"],
                        ["r = list(I())"], "result"),
    "resume_after_stop": (["class I:\n    def __init__(self):\n        self.n = 0\n    def __iter__(self):\n        return self\n    def __next__(self):\n        ev('I.__next__')\n        self.n += 1\n        if self.n == 2 or self.n > 4:\n            raise StopIteration\n        return self.n\n    def __repr__(self):\n        return 'I()'\n",
                           "it = I()"], ["r = (list(it), list(it))"], "result"),
    "length_hint_raises": (["class H:\n    def __iter__(self):\n        return iter([1, 2])\n    def __length_hint__(self):\n        ev('H.__length_hint__')\n        raise ValueError('hint')\n    def __repr__(self):\n        return 'H()'\n"],
                           ["r = list(H())"], "raises:ValueError"),
    "length_hint_notimpl": (["class H:\n    def __iter__(self):\n        return iter([1, 2])\n    def __length_hint__(self):\n        ev('H.__length_hint__')\n        return NotImplemented\n    def __repr__(self):\n        return 'H()'\n"],
                            ["r = list(H())"], "result"),
    "length_hint_negative": (["class H:\n    def __iter__(self):\n        return iter([1, 2])\n    def __length_hint__(self):\n        ev('H.__length_hint__')\n        return -1\n    def __repr__(self):\n        return 'H()'\n"],
                             ["r = list(H())"], "raises:ValueError"),
    "len_negative": (["class H:\n    def __iter__(self):\n        return iter([1, 2])\n    def __len__(self):\n        ev('H.__len__')\n        return -1\n    def __repr__(self):\n        return 'H()'\n"],
                     ["r = list(H())"], "raises:ValueError"),
    "next_raises_in_zip": (["class I:\n    def __init__(self):\n        self.n = 0\n    def __iter__(self):\n        return self\n    def __next__(self):\n        ev('I.__next__')\n        self.n += 1\n        if self.n == 2:\n            raise ValueError('boom')\n        return self.n\n    def __repr__(self):\n        return 'I()'\n"],
                           ["r = list(zip(I(), [1, 2, 3]))"], "raises:ValueError"),
    "unpack_too_many": ([], ["a, b = [1, 2, 3]", "r = a"], "raises:ValueError"),
    "next_raises_sum": (["class I:\n    def __iter__(self):\n        return self\n    def __next__(self):\n        ev('I.__next__')\n        raise ValueError('s')\n    def __repr__(self):\n        return 'I()'\n"],
                        ["r = sum(I())"], "raises:ValueError"),
    "next_raises_sorted": (["class I:\n    def __iter__(self):\n        return self\n    def __next__(self):\n        ev('I.__next__')\n        raise ValueError('s')\n    def __repr__(self):\n        return 'I()'\n"],
                           ["r = sorted(I())"], "raises:ValueError"),
    "next_raises_join": (["class I:\n    def __iter__(self):\n        return self\n    def __next__(self):\n        ev('I.__next__')\n        raise ValueError('j')\n    def __repr__(self):\n        return 'I()'\n"],
                         ["r = ''.join(I())"], "raises:ValueError"),
    "next_raises_dict": (["class I:\n    def __iter__(self):\n        return self\n    def __next__(self):\n        ev('I.__next__')\n        raise ValueError('d')\n    def __repr__(self):\n        return 'I()'\n"],
                         ["r = dict(I())"], "raises:ValueError"),
    "next_raises_star": (["class I:\n    def __iter__(self):\n        return self\n    def __next__(self):\n        ev('I.__next__')\n        raise ValueError('x')\n    def __repr__(self):\n        return 'I()'\n"],
                         ["r = [*I()]"], "raises:ValueError"),
}

# A7: attributes of built-in objects.
A7_OBJECTS = ["int", "str", "list", "dict", "print", "len", "(1).__add__", "[].append",
              "type", "object", "Exception", "range(2)", "'ab'", "3", "None", "exit"]


def a7_cases():
    cases = []
    for obj in A7_OBJECTS:
        tag = obj.replace("(", "").replace(")", "").replace("[", "").replace("]", "") \
                 .replace(".", "_").replace("'", "q").replace(" ", "")
        for kind, op in [("setattr", ["x.tag = 1", "r = x.tag"]),
                         ("delattr", ["del x.__doc__", "r = 0"]),
                         ("hasattr", ["r = (hasattr(x, 'tag'), hasattr(x, '__doc__'))"]),
                         ("getattr-default", ["r = getattr(x, 'tag', 'none')"])]:
            expect = "any" if kind in ("setattr", "delattr") else "result"
            cases.append(Case(f"a7_{tag}_{kind}", "metadata", "A7", kind, kind, op, [],
                              [f"x = {obj}"], expect))
    return cases


def table_cases(prefix, group, axis, table):
    out = []
    for name, (setup, op, expect) in table.items():
        classes = [s for s in setup if s.startswith("class ")]
        rest = [s for s in setup if not s.startswith("class ")]
        out.append(Case(f"{prefix}_{name}", group, axis, name, name, op, classes, rest,
                        expect))
    return out


# ---------------------------------------------------------------------------------------------
# Methods of the built-in types (A1 on self and on the first argument, A8 binding errors)

# (type, method, arguments as written, kind of the first argument or None, expected outcome
# with an exact self).
METHODS = [
    ("str", "upper", "", None), ("str", "lower", "", None), ("str", "casefold", "", None),
    ("str", "swapcase", "", None), ("str", "capitalize", "", None), ("str", "title", "", None),
    ("str", "isalpha", "", None), ("str", "isdigit", "", None), ("str", "isspace", "", None),
    ("str", "isidentifier", "", None), ("str", "isascii", "", None),
    ("str", "find", "'b'", "str"), ("str", "rfind", "'b'", "str"), ("str", "index", "'b'", "str"),
    ("str", "count", "'b'", "str"), ("str", "startswith", "'a'", "str"),
    ("str", "endswith", "'b'", "str"), ("str", "replace", "'a', 'z'", "str"),
    ("str", "split", "'b'", "str"), ("str", "rsplit", "'a'", "str"),
    ("str", "splitlines", "", None), ("str", "partition", "'a'", "str"),
    ("str", "rpartition", "'b'", "str"), ("str", "strip", "'a'", "str"),
    ("str", "lstrip", "", None), ("str", "rstrip", "", None),
    ("str", "removeprefix", "'a'", "str"), ("str", "removesuffix", "'b'", "str"),
    ("str", "ljust", "5", "int"), ("str", "rjust", "5", "int"), ("str", "center", "5", "int"),
    ("str", "zfill", "5", "int"), ("str", "expandtabs", "4", "int"),
    ("str", "join", "['x', 'y']", "iter_str"), ("str", "encode", "", None),
    ("str", "format", "1", "obj"), ("str", "translate", "{97: 'z'}", "map"),
    ("bytes", "__len__", "", None),
    ("list", "append", "3", "obj"), ("list", "clear", "", None), ("list", "copy", "", None),
    ("list", "reverse", "", None), ("list", "pop", "", None), ("list", "insert", "0, 9", "int"),
    ("list", "extend", "[3]", "iter"), ("list", "index", "1", "obj"),
    ("list", "count", "1", "obj"), ("list", "remove", "1", "obj"), ("list", "sort", "", None),
    ("tuple", "count", "1", "obj"), ("tuple", "index", "2", "obj"),
    ("range", "count", "1", "obj"), ("range", "index", "2", "obj"),
    ("dict", "get", "'b'", "obj"), ("dict", "setdefault", "'c', 3", "obj"),
    ("dict", "pop", "'a'", "obj"), ("dict", "popitem", "", None), ("dict", "clear", "", None),
    ("dict", "copy", "", None), ("dict", "update", "{'c': 3}", "map"),
    ("dict", "keys", "", None), ("dict", "values", "", None), ("dict", "items", "", None),
    ("set", "add", "3", "obj"), ("set", "remove", "1", "obj"), ("set", "discard", "2", "obj"),
    ("set", "pop", "", None), ("set", "clear", "", None), ("set", "copy", "", None),
    ("set", "update", "[3]", "iter"), ("set", "union", "[3]", "iter"),
    ("set", "intersection", "[1]", "iter"), ("set", "difference", "[1]", "iter"),
    ("set", "symmetric_difference", "[1, 3]", "iter"), ("set", "issubset", "[1, 2, 3]", "iter"),
    ("set", "issuperset", "[1]", "iter"), ("set", "isdisjoint", "[5]", "iter"),
    ("set", "intersection_update", "[1]", "iter"), ("set", "difference_update", "[1]", "iter"),
    ("frozenset", "union", "[3]", "iter"), ("frozenset", "copy", "", None),
    ("frozenset", "issubset", "[1, 2, 3]", "iter"),
]

# For each kind of argument: a subclass value, and a user object that implements its protocol.
ARG_KINDS = {
    "str": ("Sarg('b')", "class Sarg(str):\n    pass\n", None),
    "int": ("Iarg(5)", "class Iarg(int):\n    pass\n",
            "class Uarg:\n    def __index__(self):\n        ev('Uarg.__index__')\n        return 5\n    def __repr__(self):\n        return 'Uarg()'\n"),
    "iter": ("Larg([3])", "class Larg(list):\n    def __iter__(self):\n        ev('Larg.__iter__')\n        return iter([4])\n    def __repr__(self):\n        return 'Larg()'\n",
             "class Uarg:\n    def __iter__(self):\n        ev('Uarg.__iter__')\n        return iter([3])\n    def __repr__(self):\n        return 'Uarg()'\n"),
    "iter_str": ("Larg(['x'])", "class Larg(list):\n    def __iter__(self):\n        ev('Larg.__iter__')\n        return iter(['w'])\n    def __repr__(self):\n        return 'Larg()'\n",
                 "class Uarg:\n    def __iter__(self):\n        ev('Uarg.__iter__')\n        return iter(['u'])\n    def __repr__(self):\n        return 'Uarg()'\n"),
    "map": ("Darg({97: 'z'})", "class Darg(dict):\n    def keys(self):\n        ev('Darg.keys')\n        return [98]\n    def __getitem__(self, k):\n        ev('Darg.__getitem__')\n        return 'y'\n    def __repr__(self):\n        return 'Darg()'\n",
            "class Uarg:\n    def keys(self):\n        ev('Uarg.keys')\n        return [97]\n    def __getitem__(self, k):\n        ev('Uarg.__getitem__')\n        return 'q'\n    def __repr__(self):\n        return 'Uarg()'\n"),
    "obj": ("Iarg(1)", "class Iarg(int):\n    pass\n",
            "class Uarg:\n    def __eq__(self, o):\n        ev('Uarg.__eq__')\n        return o == 1\n    def __hash__(self):\n        ev('Uarg.__hash__')\n        return 1\n    def __repr__(self):\n        return 'Uarg()'\n"),
}


def split_first(args):
    """The first argument of `args`, and the rest with its leading comma."""
    depth = 0
    for i, ch in enumerate(args):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == "," and depth == 0:
            return args[:i], args[i:]
    return args, ""


# Expected outcomes that differ from the defaults, by (type, method, case kind).
METHOD_EXPECT = {
    ("str", "format", "too-many"): "result", ("str", "format", "too-many-sub"): "result",
    ("str", "format", "bad-keyword"): "result", ("dict", "update", "bad-keyword"): "result",
}


# Method cases whose only observation is a `None` result that the run without the operation
# prints too, so they would test nothing: a lookup or a removal of a missing object.
UNOBSERVED = {("dict", "get", "arg-user-not"), ("set", "discard", "arg-user-not")}

# The receivers of the method cases: values that each method changes or finds something in.
METHOD_LIT = {"list": "[2, 1, 3]"}


def obj_arg(first):
    """The subclass value, its class, and a user class equal to `first`, for an argument of any
    type that a method compares with its items."""
    if first.startswith("'"):
        return (f"Sarg({first})", "class Sarg(str):\n    pass\n",
                f"class Uarg:\n    def __eq__(self, o):\n        return o == {first}\n"
                f"    def __hash__(self):\n        return hash({first})\n{repr_line('Uarg')}")
    return (f"Iarg({first})", "class Iarg(int):\n    pass\n",
            f"class Uarg:\n    def __eq__(self, o):\n        return o == {first}\n"
            f"    def __hash__(self):\n        return hash({first})\n{repr_line('Uarg')}")


def method_cases():
    cases = []
    for (t, m, args, akind) in METHODS:
        lit = METHOD_LIT.get(t, EXACT[t])
        selves = [("exact", [], [f"x = {lit}"])]
        if t in SUBCLASSABLE:
            n, c = subclass(t, "Self")
            selves.append(("sub", [c], [f"x = {n}({lit})"]))
            n2 = cls_name(t, "Selfo")
            body = method("__iter__", "self", ["return iter([" + ("'k'" if t in ("dict",) else "1") + "])"], n2)
            body += method("__len__", "self", ["return 1"], n2)
            if t == "dict":
                body += method("keys", "self", ["return ['k']"], n2)
                body += method("__getitem__", "self, k", ["return 0"], n2)
            _, c2 = subclass(t, "Selfo", body)
            selves.append(("sub-over-other", [c2], [f"x = {n2}({lit})"]))
        call = f"x.{m}({args})"
        for sk, cl, st in selves:
            cases.append(Case(f"m_{t}_{m}_self_{sk}", "methods", "A1", "self-" + sk,
                              f"{t}.{m}", [f"r = {call}"], list(cl), list(st),
                              METHOD_EXPECT.get((t, m, "self-" + sk), "result"),
                              "x" if sk.startswith("sub") else "",
                              [(t, m)] if sk in ("exact", "sub") else [], "x"))
        if akind:
            first, rest = split_first(args)
            sub, subcls, user = obj_arg(first) if akind == "obj" else ARG_KINDS[akind]
            variants = [("arg-sub", sub, [subcls], "result")]
            if user:
                variants.append(("arg-user", "Uarg()", [user], "result"))
            variants.append(("arg-user-not", "Plain()",
                             ["class Plain:\n" + repr_line("Plain")], "any"))
            for ak, aexpr, acl, exp in variants:
                if (t, m, ak) in UNOBSERVED:
                    continue
                cases.append(Case(f"m_{t}_{m}_{ak}", "methods", "A1", ak, f"{t}.{m}",
                                  [f"r = x.{m}({aexpr}{rest})"], acl, [f"x = {lit}"],
                                  METHOD_EXPECT.get((t, m, ak), exp), receiver="x"))
        # A8: binding errors.
        extra = (args + ", " if args else "") + "1, 2, 3"
        cases.append(Case(f"m_{t}_{m}_too_many", "methods", "A8", "too-many", f"{t}.{m}",
                          [f"r = x.{m}({extra})"], [], [f"x = {lit}"],
                          METHOD_EXPECT.get((t, m, "too-many"), "raises:TypeError")))
        if t in SUBCLASSABLE:
            n, c = subclass(t, "Selfe")
            cases.append(Case(f"m_{t}_{m}_too_many_sub", "methods", "A8", "too-many-sub",
                              f"{t}.{m}", [f"r = x.{m}({extra})"], [c], [f"x = {n}({lit})"],
                              METHOD_EXPECT.get((t, m, "too-many-sub"), "raises:TypeError")))
        cases.append(Case(f"m_{t}_{m}_bad_keyword", "methods", "A8", "bad-keyword",
                          f"{t}.{m}", [f"r = x.{m}(zz=1)"], [], [f"x = {lit}"],
                          METHOD_EXPECT.get((t, m, "bad-keyword"), "raises:TypeError")))
    return cases


# ---------------------------------------------------------------------------------------------
# Regression cases: one program for each wrong result found earlier.

REGRESSIONS = {
    "1_iter_sentinel_reenter": (["it = None",
                                 "def f():\n    ev('f')\n    return list(it)"],
                                ["it = iter(f, None)", "r = next(it, 'end')"], "any"),
    "4_dict_or_subclass": (["class D(dict):\n    def keys(self):\n        ev('D.keys')\n        return ['a']\n    def __getitem__(self, k):\n        ev('D.__getitem__')\n        return 'sub'\n    def __repr__(self):\n        return 'D()'\n"],
                           ["r = sorted(({'z': 0} | D(a=1)).items())"], "result"),
    "6_str_sub_keyword": (["class K(str):\n    pass\n"],
                          ["r = sorted(dict(**{K('a'): 1}))"], "result"),
    "7_subtype_self_error": (["class L(list):\n    pass\n"], ["r = L().append()"],
                             "raises:TypeError"),
    "8_exc_str": ([], ["r = (str(KeyError('a')), repr(ValueError(1, 2)), str(Exception()))"],
                  "result"),
    # reg_12 and reg_16: a % whose left operand is an int and whose right operand is a tuple.
    # CPython raises TypeError.
    "12_mod_fold": ([], ["r = (-1) % (2,)"], "raises:TypeError"),
    "14_mappingproxy_or": (["class U:\n    def __ror__(self, o):\n        ev('U.__ror__')\n        return 'ror'\n    def __repr__(self):\n        return 'U()'\n"],
                           ["r = type.__dict__ | U()"], "result"),
    "15_str_sub_name": (["class N(str):\n    pass\n"],
                        ["C = type(N('C'), (), {})", "r = C.__name__"], "result"),
    "16_mod_fold_index": ([], ["r = ('a', 1)[1] % (2,)"], "raises:TypeError"),
    "17_hash_int_sub": (["class I(int):\n    pass\n",
                         "class K:\n    def __hash__(self):\n        ev('K.__hash__')\n        return I(7)\n    def __repr__(self):\n        return 'K()'\n"],
                        ["r = (hash(K()), len({K(): 1}))"], "result"),
    "18_set_sub_in_set": (["class S(set):\n    pass\n"],
                          ["r = S([5]) in {frozenset([5])}"], "result"),
    "19_property_iter": (["class A:\n    @property\n    def __iter__(self):\n        ev('A.__iter__')\n        return lambda: iter([1])\n    def __repr__(self):\n        return 'A()'\n"],
                         ["r = [v for v in A()]"], "result"),
    "20_str_sub_format": (["class S(str):\n    pass\n"],
                          ["x = S('ab')", "r = (type(format(x, '')).__name__, type('%s' % x).__name__, format(x, '') is x)"],
                          "result"),
    "lib_repr_in_int_error": (["class S(str):\n    def __repr__(self):\n        return 'SREPR'\n"],
                              ["r = int(S('zz'))"], "raises:ValueError"),
    "lib_split_identity": (["class S(str):\n    pass\n"],
                           ["x = S('ab')", "r = (x.split()[0] is x, x.partition('z')[0] is x, type(x.split()[0]).__name__)"],
                           "result"),
    "lib_dict_copy_iter": (["class D(dict):\n    def __iter__(self):\n        ev('D.__iter__')\n        return iter(['zz'])\n    def __repr__(self):\n        return 'D()'\n"],
                           ["r = sorted(D(a=1).copy().items())"], "result"),
    "lib_huge_width": ([], ["r = 'x'.zfill(-5) + 'y'.ljust(0)"], "result"),
    "2_getitem_iter_reenter": (["class G:\n    done = False\n    def __getitem__(self, i):\n        if i == 0 and not G.done:\n            G.done = True\n            next(it)\n        if i > 3:\n            raise IndexError(i)\n        return i\n    def __repr__(self):\n        return 'G()'\n"],
                               ["it = iter(G())", "r = list(it)"], "result"),
    "3_length_hint_reenter": (["class S:\n    done = False\n    def __getitem__(self, i):\n        if i > 3:\n            raise IndexError(i)\n        return i\n    def __len__(self):\n        if not S.done:\n            S.done = True\n            next(it)\n        return 4\n    def __repr__(self):\n        return 'S()'\n"],
                              ["it = iter(S())", "r = list(it)"], "result"),
    # reg_9: recursion only in C, through `repr` and `==` of lists nested 20,000 deep, built in a
    # function so that no deep value stays in the globals.
    "9_c_depth_repr": (["def deep():\n    x = []\n    for i in range(20000):\n        x = [x]\n    return x",
                        "def f():\n    return len(repr(deep()))"], ["r = f()"],
                       "raises:RecursionError"),
    "9_c_depth_eq": (["def deep():\n    x = []\n    for i in range(20000):\n        x = [x]\n    return x",
                      "def f():\n    return deep() == deep()"], ["r = f()"],
                     "raises:RecursionError"),
    "10_mutable_builtin_types": ([], ["r = []",
                                      "for t in (ExceptionGroup, type(copyright), type(exit), type(help)):\n    t.tag = 1\n    r.append((t.__name__, t.tag))"],
                                 "result"),
    "11_exit_attribute": ([], ["exit.tag = 1", "r = exit.tag"], "result"),
    "13_dict_walk_after_deletes": ([], ["d = dict.fromkeys(range(10))",
                                        "for i in range(8):\n    del d[i]",
                                        "d['x'] = 1", "d[0] = 2", "r = list(d)"], "result"),
    "13_dict_resize_after_deletes": ([], ["d = {}", "for i in range(20):\n    d[i] = i",
                                          "for i in range(18):\n    del d[i]",
                                          "for i in range(30, 40):\n    d[i] = i",
                                          "r = (list(d), list(d.items())[:3])"], "result"),
}

# The A1 results: a built-in that may return its own argument, and dunders that return an
# instance of a subclass where the built-in type is expected.
RESULTS = {
    "str_sub_add_empty": (["class S(str):\n    pass\n"],
                          ["x = S('ab')", "r = (type(x + '').__name__, x + '' is x)"], "result"),
    "str_sub_mul_one": (["class S(str):\n    pass\n"],
                        ["x = S('ab')", "r = (type(x * 1).__name__, x * 1 is x)"], "result"),
    # A % whose non-empty format has no % gives back the format itself; an empty one gives ''.
    "str_sub_mod_no_spec": (["class S(str):\n    pass\n"],
                            ["x = S('ab')",
                             "r = (x % () is x, x % {} is x, x % [] is x, type(S('') % ()).__name__)"],
                            "result"),
    "tuple_sub_add_empty": (["class T(tuple):\n    pass\n"],
                            ["x = T((1,))", "r = (type(x + ()).__name__, x + () is x)"], "result"),
    "str_returns_str_sub": (["class S(str):\n    pass\n",
                             "class A:\n    def __str__(self):\n        return S('s')\n    def __repr__(self):\n        return S('r')\n    def __format__(self, spec):\n        return S('f')\n"],
                            ["a = A()", "r = (type(str(a)).__name__, type(repr(a)).__name__, type(format(a, '')).__name__, type(f'{a}').__name__, type('%s' % a).__name__)"],
                            "result"),
    "len_returns_int_sub": (["class I(int):\n    pass\n",
                             "class A:\n    def __len__(self):\n        return I(3)\n    def __repr__(self):\n        return 'A()'\n"],
                            ["r = (len(A()), type(len(A())).__name__, bool(A()))"], "result"),
    "index_returns_int_sub": (["class I(int):\n    pass\n",
                               "class A:\n    def __index__(self):\n        return I(1)\n    def __repr__(self):\n        return 'A()'\n"],
                              ["r = [10, 20][A()]"], "any"),
    "bool_returns_int": (["class A:\n    def __bool__(self):\n        return 1\n    def __repr__(self):\n        return 'A()'\n"],
                         ["r = bool(A())"], "raises:TypeError"),
    "int_returns_int_sub": (["class I(int):\n    pass\n",
                             "class A:\n    def __int__(self):\n        return I(4)\n    def __repr__(self):\n        return 'A()'\n"],
                            ["r = (int(A()), type(int(A())).__name__)"], "result"),
}


# Fast paths: for each path of the model that skips the generic protocol on an assumption, a
# case that breaks the assumption (a subclass that overrides the skipped dunder, user code in the
# skipped call, or a non-function descriptor).
def _cls(name, base, methods):
    body = "".join(method(m, p, b, name) for (m, p, b) in methods)
    return f"class {name}{'(' + base + ')' if base else ''}:\n{body}{repr_line(name)}"


FAST = {
    "num_sub_add": ([_cls("I", "int", [("__add__", "self, o", ["return 'over'"])])],
                    ["r = I(1) + 1"], "result"),
    "str_sub_eq": ([_cls("S", "str", [("__eq__", "self, o", ["return 'eq'"])])],
                   ["r = S('a') == 'a'"], "result"),
    "tuple_sub_lt": ([_cls("T", "tuple", [("__lt__", "self, o", ["return 'lt'"])])],
                     ["r = T((1,)) < (2,)"], "result"),
    "list_sub_truth": ([_cls("L", "list", [("__len__", "self", ["return 0"])])],
                       ["r = bool(L([1]))"], "result"),
    "identity_in": ([_cls("E", "", [("__eq__", "self, o", ["raise ValueError('eq')"])])],
                    ["e = E()", "r = (e in [e], [e].count(e), [e].index(e))"], "result"),
    "tryslot_radd": ([_cls("U", "", [("__radd__", "self, o", ["return 'radd'"])])],
                     ["r = [1] + U()"], "result"),
    "tryslot_rmul": ([_cls("U", "", [("__rmul__", "self, o", ["return 'rmul'"])])],
                     ["r = ('a' * U(), [1] * U())"], "result"),
    "hash_eq_only": ([_cls("Q", "", [("__eq__", "self, o", ["return True"])])],
                     ["r = hash(Q())"], "raises:TypeError"),
    "dict_key_int_sub_eq": ([_cls("I", "int", [("__eq__", "self, o", ["return True"])]) +
                             "    __hash__ = int.__hash__\n"],
                            ["d = {1: 'a'}", "r = (d[I(1)], I(1) in {1})"], "result"),
    "set_update_sub_iter": ([_cls("Ss", "set", [("__iter__", "self", ["return iter([9])"])])],
                            ["s = {1}", "s.update(Ss({2}))", "r = sorted(s)"], "result"),
    "dict_merge_getitem": ([_cls("D", "dict", [("__getitem__", "self, k", ["return 'x'"])])],
                           ["r = ({**D(a=1)}, dict(D(a=1)))"], "result"),
    "sort_int_sub_lt": ([_cls("I", "int", [("__lt__", "self, o", ["return int.__lt__(self, o)"])])],
                        ["r = sorted([I(2), I(1), I(3)])"], "result"),
    "orderfree_sub": ([_cls("I", "int", [("__lt__", "self, o", ["return int.__lt__(self, o)"]),
                                        ("__gt__", "self, o", ["return int.__gt__(self, o)"])])
                       + "    __hash__ = int.__hash__\n"],
                      ["r = (min({I(3), 1}), max({I(3), 1}))"], "result"),
    "sum_float_int_sub": ([_cls("I", "int", [("__radd__", "self, o", ["return 'radd'"])])],
                          ["r = (sum([1.5, I(2)]), sum([1, I(2)]))"], "result"),
    "fromkeys_sub": ([_cls("D", "dict", [("__setitem__", "self, k, v",
                                          ["dict.__setitem__(self, k, v)"])])],
                     ["r = sorted(D.fromkeys(['a', 'b']).items())"], "result"),
    "isinstance_exact_meta": (["class M(type):\n    def __instancecheck__(cls, o):\n        ev('M.__instancecheck__')\n        return False\n",
                               "class C(metaclass=M):\n    pass\n"],
                              ["r = (isinstance(C(), C), isinstance(1, C))"], "result"),
    "unbound_sub_self": ([_cls("L", "list", [])], ["x = L()", "list.append(x, 1)",
                                                   "r = (list.__len__(x), x)"], "result"),
    "str_of_str_sub": ([_cls("S", "str", [("__str__", "self", ["return 'over'"])])],
                       ["r = (str(S('a')), '%s' % S('a'), f'{S(\"a\")}')"], "result"),
    "format_empty_spec_int_sub": ([_cls("I", "int", [("__format__", "self, spec",
                                                      ["return 'fmt'"])])],
                                  ["r = (format(I(1), ''), f'{I(1)}')"], "result"),
    "extend_tuple_sub_iter": ([_cls("T", "tuple", [("__iter__", "self", ["return iter([9])"])])],
                              ["r = ([*T((1,))], list(T((1,))), (lambda *a: a)(*T((1,))))"],
                              "result"),
    "len_list_sub": ([_cls("L", "list", [("__len__", "self", ["return 7"])])],
                     ["r = (len(L([1])), L([1]).__len__())"], "result"),
    "repr_list_with_sub_items": ([_cls("I", "int", [("__repr__", "self", ["return 'I!'"])])],
                                 ["r = repr([I(1), (I(2),), {I(3): I(4)}])"], "result"),
}


def regression_cases():
    return table_cases("reg", "regressions", "regression", REGRESSIONS)


def all_cases():
    cases = (a1_cases() + method_cases() + a3_cases() + a4_cases()
             + table_cases("a2", "reentry", "A2", A2)
             + table_cases("a5", "limits", "A5", A5)
             + table_cases("a6", "iteration", "A6", A6)
             + a7_cases() + table_cases("fast", "fast-paths", "fast", FAST)
             + table_cases("res", "results", "A1", RESULTS)
             + regression_cases())
    seen = set()
    for c in cases:
        if c.id in seen:
            raise ValueError(f"duplicate case id {c.id}")
        seen.add(c.id)
    return cases
