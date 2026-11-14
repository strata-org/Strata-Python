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

import pathlib
import re
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
    # The built-in functions and methods that the case calls by name, as `<type>.<name>` or a
    # function's name; CPython's run must show each of them (`cpython_calls.py`).
    calls: list = field(default_factory=list)
    # The attributes of `typing` and `dataclasses` that the case reads, as `<module>.<name>`
    # (declared: CPython shows no call for an attribute read).
    reads: list = field(default_factory=list)


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
    Op("star_kwargs", "(lambda **k: k)(**{x})", "keys", "['a']",
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
                                  and (op.name, base, lk) not in FAST_SKIPS
                                  else [],
                                  calls=op_calls(op) if lk in ("exact", "sub") and
                                  rk in ("exact", "sub") else []))
    return cases


def op_calls(op):
    """The built-in function or class that the operation `op` calls by name, if any: `len` for
    `len({x})`, `list.__new__` for `list({x})`."""
    m = re.match(r"(?:sorted\()?(\w+)\(", op.expr)
    if not m:
        return []
    name = m.group(1)
    if name in ("list", "tuple", "dict", "set", "int", "float", "str", "bool"):
        return [f"{name}.__new__"]
    if name in ("len", "repr", "format", "hash", "abs", "next", "iter", "sorted", "sum", "max",
                "any", "isinstance", "print"):
        return [name]
    return []


# The (operation, type, kind) whose operand CPython 3.12 handles on a fast path, without the dunder
# entry that the operation reaches otherwise, so the case gives no evidence for that entry: an
# exact `int` or `str` in `format` (`PyObject_Format`), an exact `str` in `str()` and `print`
# (`PyObject_Str`), an exact `int` in `int()` and `float` in `float()`, any `int` as an index
# (`_PyNumber_Index`), `True` in a truth test, an exact `list` or `tuple` read by `list_extend` and
# `PySequence_Tuple`, any frozenset merged by `set_merge`, any dict with `dict.__iter__` merged by
# `dict_merge`.
FAST_SKIPS = (
    {(op, t, "exact") for op in ("format", "fstring") for t in ("int", "str")}
    | {(op, "str", "exact") for op in ("str", "print")}
    | {("int", "int", "exact"), ("float", "float", "exact")}
    | {("index", t, k) for t in ("int", "bool") for k in ("exact", "sub")}
    | {(op, "bool", "exact") for op in ("not", "truthy", "bool")}
    | {(op, t, "exact") for op in ("star_list", "star_args", "list_of", "sorted", "tuple_of")
       for t in ("list", "tuple")}
    | {(op, "frozenset", k) for op in ("star_set", "set_of", "list_of", "sorted")
       for k in ("exact", "sub")}
    | {(op, "dict", k) for op in ("star_kwargs", "dict_display", "dict_of")
       for k in ("exact", "sub")}
)


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


def table_cases(prefix, group, axis, table, calls=None, entries=None):
    """The cases of a table of `name: (setup, operation, expected outcome)`, with the names that
    each case calls (`calls`) and the dunder entries that its operation reaches (`entries`)."""
    out = []
    for name, (setup, op, expect) in table.items():
        classes = [s for s in setup if s.startswith("class ")]
        rest = [s for s in setup if not s.startswith("class ")]
        out.append(Case(f"{prefix}_{name}", group, axis, name, name, op, classes, rest,
                        expect, entries=(entries or {}).get(name, []),
                        calls=(calls or {}).get(name, [])))
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
                              [], "x", calls=[f"{t}.{m}"] if sk != "sub-over-other" else []))
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
                                  METHOD_EXPECT.get((t, m, ak), exp), receiver="x",
                                  calls=[f"{t}.{m}"]))
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
    # Found by the fuzzer, outside its build seed.
    "fuzz_str_sub_in_str": (["class S(str):\n    pass\n"], ["r = S('a') in 'ab'"], "result"),
    "fuzz_list_sub_radd_other": (["class L(list):\n    def __radd__(self, o):\n        ev('L.__radd__')\n        return 'L.radd'\n    def __repr__(self):\n        return 'L()'\n",
                                  "class U:\n    def __radd__(self, o):\n        ev('U.__radd__')\n        return 'U.radd'\n"],
                                 ["r = L([1]) + U()"], "raises:TypeError"),
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


# ---------------------------------------------------------------------------------------------
# Direct calls: each method of a built-in type called by name, on a receiver of that type, so that
# every entry of the model's tables is reached at least once, also those that no syntax reaches
# (`int.__rsub__`, `dict_keys.isdisjoint`). The names come from `vars(T)` of CPython 3.12.

# A receiver of each type, and the arguments for a one-argument method: an element (for
# `__contains__`, `index`, `count`) and another value of a fitting kind.
RECEIVERS = {
    "int": ("3", "2"), "bool": ("True", "False"), "float": ("1.5", "2.0"),
    "str": ("'ab'", "'b'"), "bytes": ("b'ab'", "b'b'"), "tuple": ("(1, 2)", "(3,)"),
    "list": ("[2, 1]", "[3]"), "dict": ("{'a': 1}", "{'b': 2}"),
    "set": ("{1, 2}", "{2, 3}"), "frozenset": ("frozenset({1, 2})", "frozenset({2, 3})"),
    "range": ("range(3)", "range(2)"), "object": ("object()", "object()"),
    "dict_keys": ("{'a': 1}.keys()", "{'a', 'b'}"), "dict_items": ("{'a': 1}.items()", "{('a', 1)}"),
    "dict_values": ("{'a': 1}.values()", "1"),
    "list_iterator": ("iter([1, 2])", "1"), "tuple_iterator": ("iter((1, 2))", "1"),
    "str_ascii_iterator": ("iter('ab')", "1"), "str_iterator": ("iter('\\u00e9b')", "1"),
    "bytes_iterator": ("iter(b'ab')", "1"), "range_iterator": ("iter(range(3))", "1"),
    "longrange_iterator": ("iter(range(2 ** 70, 2 ** 70 + 2))", "1"),
    "set_iterator": ("iter({1, 2})", "1"),
    "dict_keyiterator": ("iter({'a': 1})", "1"), "dict_valueiterator": ("iter({'a': 1}.values())", "1"),
    "dict_itemiterator": ("iter({'a': 1}.items())", "1"),
    "list_reverseiterator": ("reversed([1, 2])", "1"),
    "dict_reversekeyiterator": ("reversed({'a': 1})", "1"),
    "dict_reversevalueiterator": ("reversed({'a': 1}.values())", "1"),
    "dict_reverseitemiterator": ("reversed({'a': 1}.items())", "1"),
    "reversed": ("reversed((1, 2))", "1"), "enumerate": ("enumerate('ab')", "1"),
    "zip": ("zip('ab', [1, 2])", "1"),
    "BaseException": ("BaseException('a', 1)", "'note'"), "Exception": ("Exception('a')", "'n'"),
    "ValueError": ("ValueError('a')", "'n'"), "KeyError": ("KeyError('k')", "'n'"),
    "OSError": ("OSError(2, 'no')", "'n'"), "StopIteration": ("StopIteration(5)", "'n'"),
    "SystemExit": ("SystemExit(3)", "'n'"), "NameError": ("NameError('x', name='x')", "'n'"),
    "AttributeError": ("AttributeError('x', name='a', obj=1)", "'n'"),
    "ImportError": ("ImportError('x', name='m')", "'n'"),
    "BaseExceptionGroup": ("BaseExceptionGroup('g', [ValueError(1)])", "'n'"),
    "UnicodeDecodeError": ("UnicodeDecodeError('utf-8', b'x', 0, 1, 'bad')", "'n'"),
    "UnicodeEncodeError": ("UnicodeEncodeError('ascii', 'x', 0, 1, 'bad')", "'n'"),
    "property": ("property(lambda s: 1)", "lambda s: 2"),
    "classmethod": ("classmethod(lambda c: 1)", "1"), "staticmethod": ("staticmethod(lambda: 1)", "1"),
    "type": ("int", "str"), "super": ("super(int, 3)", "1"), "slice": ("slice(1, 2)", "1"),
}

# Methods left out: their result depends on the machine or the interpreter's internals.
DIRECT_SKIP = {"__sizeof__", "__reduce__", "__reduce_ex__", "__getstate__", "__setstate__",
               "__subclasshook__", "__dir__", "__getnewargs__", "__getnewargs_ex__",
               "__del__", "__instancecheck__", "__subclasscheck__", "mro", "__subclasses__",
               "__prepare__", "__new__", "__init__", "__init_subclass__", "__class_getitem__",
               # `property.__set_name__` returns None and changes nothing visible in 3.12.
               "__set_name__",
               # `bytes.__buffer__` returns a memoryview, whose repr shows its address.
               "__buffer__"}

# Direct calls whose result shows an address: only the result's type is observed.
ADDRESS_RESULTS = {("object", "__repr__"), ("object", "__str__"), ("object", "__format__"),
                   ("classmethod", "__repr__"), ("staticmethod", "__repr__")}

UNARY = {"__neg__", "__pos__", "__abs__", "__invert__", "__bool__", "__len__", "__hash__",
         "__repr__", "__str__", "__iter__", "__reversed__", "__int__", "__float__", "__index__",
         "__trunc__", "__floor__", "__ceil__", "__length_hint__", "__next__", "__bytes__",
         "__copy__", "__round__", "__complex__", "__float__"}


# Direct calls whose CPython outcome is an exception, because that is what the method does on
# its receiver: `object()` has no `__dict__`, `int` is immutable, the property has no deleter.
DIRECT_EXPECT = {
    ("object", "__setattr__"): "raises:AttributeError",
    ("object", "__delattr__"): "raises:AttributeError",
    ("type", "__setattr__"): "raises:TypeError", ("type", "__delattr__"): "raises:TypeError",
    ("property", "__delete__"): "raises:AttributeError",
    ("property", "__set__"): "raises:AttributeError",
}

# Arguments for the methods that the rules of `direct_args` don't fit.
DIRECT_ARGS = {
    ("int", "from_bytes"): "b'\\x01\\x02', 'big'", ("float", "__getformat__"): "'double'",
    ("float", "fromhex"): "'0x1p3'", ("str", "__mod__"): "()", ("bytes", "__mod__"): "()",
    ("str", "center"): "6, '*'", ("str", "ljust"): "4", ("str", "rjust"): "4",
    ("str", "replace"): "'a', 'z'", ("str", "translate"): "{97: 'z'}", ("str", "zfill"): "5",
("bytes", "center"): "6", ("bytes", "fromhex"): "'6162'",
    ("bytes", "ljust"): "4", ("bytes", "rjust"): "4", ("bytes", "replace"): "b'a', b'z'",
    ("bytes", "translate"): "None, b'a'", ("bytes", "zfill"): "5",
    ("bytes", "maketrans"): "b'ab', b'cd'", ("set", "add"): "3",
    ("BaseExceptionGroup", "derive"): "[KeyError(2)]",
    ("BaseExceptionGroup", "split"): "ValueError", ("BaseExceptionGroup", "subgroup"): "ValueError",
    ("property", "__set__"): "1, 2", ("staticmethod", "__call__"): "",
    ("type", "__call__"): "'7'", ("slice", "indices"): "5",
}


def direct_args(t, name):
    """The arguments of the direct call of `t.name`, or `None` to leave it out."""
    recv, other = RECEIVERS[t]
    if name in DIRECT_SKIP:
        return None
    if (t, name) in DIRECT_ARGS:
        return DIRECT_ARGS[(t, name)]
    if name in UNARY:
        return ""
    if name in ("__contains__", "index", "count", "remove", "discard", "__getitem__"):
        elem = {"str": "'a'", "bytes": "b'a'", "dict": "'a'", "dict_keys": "'a'",
                "dict_items": "('a', 1)", "dict_values": "1"}.get(t, "1")
        if name == "__getitem__" and t in ("str", "bytes", "tuple", "list", "range"):
            elem = "0"
        return elem
    if name in ("__setitem__",):
        return "0, 9" if t == "list" else "'z', 9"
    if name == "__delitem__":
        return "0" if t == "list" else "'a'"
    if name == "__format__":
        return "''"
    if name in ("__getattribute__", "__delattr__"):
        return "'__class__'" if name == "__getattribute__" else "'tag'"
    if name == "__setattr__":
        return "'tag', 1"
    if name in ("__set_name__",):
        return "int, 'n'"
    if name in ("__get__",):
        return "1, int"
    if name in ("setter", "getter", "deleter"):
        return other
    if name in ("update", "difference_update", "intersection_update",
                "symmetric_difference_update", "union", "intersection", "difference",
                "symmetric_difference", "issubset", "issuperset", "isdisjoint", "extend",
                "append", "join", "split", "find", "startswith", "endswith", "partition",
                "rpartition", "rsplit", "rfind", "rindex", "removeprefix", "removesuffix",
                "strip", "lstrip", "rstrip", "fromkeys", "get", "setdefault", "pop",
                "insert"):
        if t in ("set", "frozenset", "dict", "list", "str", "bytes", "dict_keys", "dict_items"):
            if name == "insert":
                return "0, 9"
            if name in ("get", "setdefault", "pop") and t == "dict":
                return "'a'"
            if name == "pop" and t in ("set", "list"):
                return ""
            if name in ("index", "rindex", "find", "rfind", "split", "rsplit", "partition",
                        "rpartition", "startswith", "endswith", "strip", "lstrip", "rstrip",
                        "removeprefix", "removesuffix", "join") and t in ("str", "bytes"):
                return {"join": "['x', 'y']" if t == "str" else "[b'x', b'y']"}.get(name, other)
            return other
    if name == "add_note":
        return other
    if name == "with_traceback":
        return "None"
    if name in ("__pow__", "__rpow__", "__rmul__", "__imul__", "__mul__"):
        return "2"
    if name == "__rmod__":
        return {"str": "'<%s>'", "bytes": "b'<%s>'"}.get(t, other)
    if name == "maketrans":
        return "'ab', 'cd'"
    if name == "format_map":
        return "{}"
    if name.startswith("__") and name.endswith("__"):
        return other
    return None


def direct_cases():
    import builtins
    cases = []
    for t in RECEIVERS:
        cls = getattr(builtins, t, None)
        if cls is None:
            cls = type(eval(RECEIVERS[t][0]))
        for name in sorted(vars(cls)):
            attr = vars(cls)[name]
            if not callable(getattr(cls, name, None)) or isinstance(attr, type) or \
                    type(attr).__name__ in ("getset_descriptor", "member_descriptor"):
                continue
            args = direct_args(t, name)
            if args is None and not (name.startswith("__") and name.endswith("__")):
                args = ""
            if args is None:
                continue
            recv = RECEIVERS[t][0]
            # Called through the type, so that a method that the receiver's class shadows (a
            # class's `__delattr__` is `type`'s, not the instance's) is the one named.
            if type(attr).__name__ in ("classmethod_descriptor", "staticmethod", "classmethod"):
                op = [f"r = type(x).{name}({args})"]
            else:
                op = [f"r = type(x).{name}(x{', ' + args if args else ''})"]
            if name == "add_note":
                op = [f"x.add_note({args})", "r = x.__notes__"]
            if (t, name) in ADDRESS_RESULTS:
                op = [f"r = type(type(x).{name}(x{', ' + args if args else ''})).__name__"]
            if name == "__hash__":
                # The hash of a str or bytes depends on the hash seed, of an object on its address.
                op = [f"r = type(x).__hash__(x) == hash(x)"]
            cases.append(Case(f"d_{t}_{name}", "direct", "direct", "direct",
                              f"{t}.{name}", op, [], [f"x = {recv}"],
                              DIRECT_EXPECT.get((t, name), "result"), receiver="x",
                              calls=[f"{t}.{name}"]))
    return cases


def defining(cls, name):
    """`<type>.<name>` for the class in the MRO of `cls` that defines `name`."""
    for c in cls.__mro__:
        if name in vars(c):
            return f"{c.__qualname__}.{name}"
    return f"{cls.__qualname__}.{name}"


# Calls of built-in classes and functions that the other groups don't make inside an operation:
# every built-in exception class, and the class statement itself.
def constructor_cases():
    import builtins
    cases = []
    for name in sorted(vars(builtins)):
        cls = vars(builtins)[name]
        # `EnvironmentError` and `IOError` are other names of `OSError`.
        if isinstance(cls, type) and issubclass(cls, BaseException) and cls.__name__ == name:
            args = {"UnicodeDecodeError": "'utf-8', b'x', 0, 1, 'bad'",
                    "UnicodeEncodeError": "'ascii', 'x', 0, 1, 'bad'",
                    "UnicodeTranslateError": "'x', 0, 1, 'bad'",
                    "BaseExceptionGroup": "'g', [ValueError(1)]",
                    "ExceptionGroup": "'g', [ValueError(1)]",
                    # The second argument of a syntax error is its location.
                    "SyntaxError": "'a', ('f', 1, 2, 'x')",
                    "IndentationError": "'a', ('f', 1, 2, 'x')",
                    "TabError": "'a', ('f', 1, 2, 'x')"}.get(name, "'a', 1")
            cases.append(Case(f"c_{name}", "constructors", "direct", "constructor", name,
                              [f"r = {name}({args})", "r = (type(r).__name__, r.args, str(r))"],
                              expect="result",
                              calls=[defining(cls, "__new__"), defining(cls, "__init__")]))
    return cases


CALLS = {
    "class_statement": ([], ["class C:\n    x = 1", "r = C.x"], "result"),
    "all": ([], ["r = (all([1, 0]), all([]))"], "result"),
    "callable": ([], ["r = (callable(len), callable(1))"], "result"),
    "divmod": ([], ["r = (divmod(7, 2), divmod(-7.5, 2))"], "result"),
    "hex": ([], ["r = (hex(255), hex(-1))"], "result"),
    "issubclass": ([], ["r = (issubclass(bool, int), issubclass(int, (str, object)))"], "result"),
    "setattr": (["class C:\n    pass\n"], ["c = C()", "setattr(c, 'a', 1)", "r = c.a"], "result"),
    "type_or": ([], ["r = (repr(int | str), repr(type.__or__(int, str)), repr(type.__ror__(str, int)))"],
                "result"),
    "type_repr": ([], ["r = (repr(int), repr(None), repr(...), repr(NotImplemented))"], "result"),
    "class_getitem": ([], ["r = (repr(list[int]), repr(dict[str, int]), repr(tuple[int, ...]), repr(set[int]), repr(frozenset[int]))"],
                      "result"),
    "maketrans": ([], ["r = sorted(str.maketrans('ab', 'cd').items())"], "result"),
    "set_iterator": ([], ["it = iter({1, 2})", "r = (next(it), it.__length_hint__())"], "result"),
    "callable_iterator": (["def f():\n    return 1\n"],
                          ["it = iter(f, 1)", "r = (iter(it) is it, next(it, 'end'))"], "result"),
    "seq_iterator": (["class G:\n    def __getitem__(self, i):\n        if i > 1:\n            raise IndexError(i)\n        return i\n    def __repr__(self):\n        return 'G()'\n"],
                     ["it = iter(G())", "r = (iter(it) is it, it.__length_hint__(), next(it), list(it))"],
                     "result"),
    "init_subclass": (["class B:\n    def __init_subclass__(cls, **kw):\n        ev('B.__init_subclass__')\n        super().__init_subclass__(**kw)\n"],
                      ["class C(B):\n    pass", "r = C.__name__"], "result"),
    "descriptor_types": ([], ["p = property(lambda s: 1)", "c = classmethod(len)", "s = staticmethod(len)",
                              "r = (type(p).__name__, type(c).__name__, type(s).__name__, s(\"ab\"))"],
                         "result"),
    "super_call": (["class B:\n    def f(self):\n        return 'B.f'\n",
                    "class C(B):\n    def f(self):\n        return super().f()\n"],
                   ["r = (C().f(), super(C, C()).f())"], "result"),
    "slice_repr": ([], ["r = repr(slice(1, None, 2))"], "result"),
    "type_three_args": ([], ["C = type('C', (), {'a': 1, '__module__': '__main__'})", "r = (C.__name__, C.a, C.__bases__)"],
                        "result"),
    "object_setattr": (["class C:\n    pass\n"],
                       ["c = C()", "object.__setattr__(c, 'a', 1)", "b = c.a", "object.__delattr__(c, 'a')",
                        "r = (b, hasattr(c, 'a'))"], "result"),
    "bytes_new": ([], ["r = (bytes([65, 66]), bytes(2), bytes('ab', 'ascii'))"], "result"),
    "enumerate_new": ([], ["r = list(enumerate('ab', 1))"], "result"),
    "property_set_name": ([], ["class C:\n    p = property(lambda s: 1)", "r = C().p"], "result"),
    "bool_invert": ([], ["r = (~True, ~False)"], "result"),
    "frozenset_ops": ([], ["a = frozenset({1, 2})", "b = frozenset({2, 3})",
                           "r = (a | b, a & b, a - b, a ^ b, a < b, a <= a, a == b, a != b, a > b, a >= a, len(a), 1 in a, hash(a) == hash(frozenset({2, 1})))"],
                      "result"),
    "set_ops": ([], ["a = {1, 2}", "b = {2, 3}",
                     "r = (a | b, a & b, a - b, a ^ b, a < b, a <= a, a == b, a != b, a > b, a >= a, len(a), 1 in a)"],
                "result"),
}


# What each case of `CALLS` calls by name, and the dunder entries it reaches implicitly.
CALLS_CALLS = {
    "object_setattr": ["object.__setattr__", "object.__delattr__"],
    "type_three_args": ["type.__new__", "type.__init__"],
    "class_statement": ["__build_class__"], "all": ["all"], "callable": ["callable"],
    "divmod": ["divmod"], "hex": ["hex"], "issubclass": ["issubclass"], "setattr": ["setattr"],
    "type_or": ["type.__or__", "type.__ror__"], "maketrans": ["str.maketrans"],
    "bytes_new": ["bytes.__new__"], "enumerate_new": ["enumerate.__new__"],
}
CALLS_ENTRIES = {
    "type_repr": [("type", "__repr__"), ("NoneType", "__repr__"), ("ellipsis", "__repr__"),
                  ("NotImplementedType", "__repr__")],
    "class_getitem": [(t, "__class_getitem__") for t in ("list", "dict", "tuple", "set",
                                                          "frozenset")],
    "callable_iterator": [("callable_iterator", "__iter__"), ("callable_iterator", "__next__")],
    "seq_iterator": [("iterator", "__iter__"), ("iterator", "__next__"),
                     ("iterator", "__length_hint__")],
    "init_subclass": [("object", "__init_subclass__")],
    "property_set_name": [("property", "__set_name__")],
    "bool_invert": [("bool", "__invert__")],
}


# Syntax that no other group reaches: the remaining operators, comprehensions, displays,
# exceptions and `with`, `assert`, conversions in f-strings, slices with steps, `global`.
SYNTAX = {
    "isub": ([], ["r = 7", "r -= 2"], "result"), "imul": ([], ["r = 7", "r *= 2"], "result"),
    "idiv": ([], ["r = 7", "r /= 2"], "result"), "ifloordiv": ([], ["r = 7", "r //= 2"], "result"),
    "imod": ([], ["r = 7", "r %= 4"], "result"), "ipow": ([], ["r = 7", "r **= 2"], "result"),
    "ilshift": ([], ["r = 7", "r <<= 2"], "result"), "irshift": ([], ["r = 7", "r >>= 1"], "result"),
    "iand": ([], ["r = 7", "r &= 3"], "result"), "ixor": ([], ["r = 7", "r ^= 3"], "result"),
    "matmul": (["class M:\n    def __matmul__(self, o):\n        return 'mm'\n    def __rmatmul__(self, o):\n        return 'rmm'\n    def __imatmul__(self, o):\n        return 'imm'\n    def __repr__(self):\n        return 'M()'\n"],
               ["m = M()", "a = m @ 1", "b = 1 @ m", "m @= 2", "r = (a, b, m)"], "result"),
    "matmul_int": ([], ["r = 2 @ 3"], "raises:TypeError"),
    "uadd": ([], ["r = (+3, +1.5, +True)"], "result"),
    "comparisons": ([], ["r = (1 <= 2, 'a' <= 'b', [1] <= [2], (1,) <= (0,), 2 > 1, 'b' > 'a')"],
                    "result"),
    "not_in": ([], ["r = (1 not in [1, 2], 'z' not in 'ab', 3 not in {1: 2})"], "result"),
    "set_comp": ([], ["r = {v % 3 for v in range(7) if v > 1}"], "result"),
    "dict_comp": ([], ["r = {v: v * v for v in range(4) if v != 2}"], "result"),
    "list_comp_nested": ([], ["r = [(a, b) for a in range(3) for b in 'xy' if a != 1]"], "result"),
    "displays": ([], ["x = [2, 3]", "d = {'b': 2}",
                      "r = ([1, *x], (*x,), (0, *x), {1, *x}, {'a': 1, **d}, {'k%d' % i: i for i in range(2)})"],
                 "result"),
    "dict_display_long": ([], ["r = {'a': 1, 'b': 2, 'c': 3, 'd': 4, 'e': 5, 'f': 6, 'g': 7, 'h': 8, 'i': 9, 'j': 10, 'k': 11, 'l': 12, 'm': 13, 'n': 14, 'o': 15, 'p': 16, 'q': 17, 'r': 18}"],
                          "result"),
    # The exceptions are caught in the operation, so that the case gives a result and its
    # instructions count for coverage; the chain shows in the result.
    "raise": ([], ["try:\n    raise ValueError('v')\nexcept ValueError as e:\n    r = (type(e).__name__, e.args)"],
              "result"),
    "raise_from": ([], ["try:\n    try:\n        raise KeyError('k')\n    except KeyError as e:\n        raise ValueError('v') from e\nexcept ValueError as e:\n    r = (type(e.__cause__).__name__, type(e.__context__).__name__, e.__suppress_context__)"],
                   "result"),
    "raise_context": ([], ["try:\n    try:\n        raise KeyError('k')\n    except KeyError:\n        raise ValueError('v')\nexcept ValueError as e:\n    r = (e.__cause__, type(e.__context__).__name__, e.__suppress_context__)"],
                      "result"),
    "bare_raise": ([], ["try:\n    try:\n        raise KeyError('k')\n    except KeyError:\n        raise\nexcept KeyError as e:\n    r = str(e)"],
                   "result"),
    "try_else_finally": ([], ["r = []", "try:\n    r.append(1)\nexcept ValueError:\n    r.append(2)\nelse:\n    r.append(3)\nfinally:\n    r.append(4)"],
                         "result"),
    "except_tuple": ([], ["r = []", "for e in (KeyError, IndexError, ValueError):\n    try:\n        raise e('x')\n    except (KeyError, IndexError) as x:\n        r.append(type(x).__name__)\n    except Exception:\n        r.append('other')"],
                     "result"),
    # The function is defined in the operation, so that its instructions are the template's.
    "finally_completions": ([], ["def f(n):\n    for i in range(3):\n        try:\n            if n == 0:\n                return 'ret'\n            if n == 1:\n                break\n            if n == 2:\n                continue\n            if n == 3:\n                raise ValueError('v')\n        finally:\n            log.append(n)\n    return 'end'",
                                 "log = []", "r = []", "for n in range(4):\n    try:\n        r.append(f(n))\n    except ValueError:\n        r.append('raised')", "r.append(log)"],
                            "result"),
    "with_in_finally": (["class CM:\n    def __enter__(self):\n        return self\n    def __exit__(self, t, v, tb):\n        return False\n    def __repr__(self):\n        return 'CM()'\n"],
                        ["r = []", "try:\n    try:\n        raise KeyError('k')\n    finally:\n        with CM():\n            r.append('in')\nexcept KeyError as e:\n    r.append(type(e).__name__)"],
                        "result"),
    "reraise_in_finally": (["class CM:\n    def __enter__(self):\n        return self\n    def __exit__(self, t, v, tb):\n        return True\n    def __repr__(self):\n        return 'CM()'\n"],
                           ["def f():\n    try:\n        raise KeyError('pending')\n    finally:\n        with CM():\n            raise",
                            "try:\n    f()\n    r = 'no'\nexcept KeyError as e:\n    r = str(e)"], "result"),
        "displays_after_star": ([], ["x = [2, 3]", "r = ([1, *x, 4], sorted({1, *x, 5}))"], "result"),
    "with": (["class CM:\n    def __enter__(self):\n        return 'in'\n    def __exit__(self, t, v, tb):\n        return t is KeyError\n    def __repr__(self):\n        return 'CM()'\n"],
             ["r = []", "with CM() as v:\n    r.append(v)", "with CM():\n    raise KeyError('swallowed')", "r.append('after')"],
             "result"),
    "with_raises": (["class CM:\n    def __enter__(self):\n        return self\n    def __exit__(self, t, v, tb):\n        return False\n    def __repr__(self):\n        return 'CM()'\n"],
                    ["with CM():\n    raise ValueError('out')"], "raises:ValueError"),
    "assert": ([], ["assert 1 == 1", "try:\n    assert 1 == 2, 'no'\nexcept AssertionError as e:\n    r = e.args"],
               "result"),
    "del_attr": (["class C:\n    pass\n"], ["c = C()", "c.a = 1", "del c.a", "r = hasattr(c, 'a')"],
                 "result"),
    "fstring_conversions": ([], ["x = 'é'", "r = f'{x!r} {x!s} {x!a} {3!r:>4}'"], "result"),
    "slice_steps": ([], ["x = list(range(6))", "x[1:3] = [9]", "del x[::2]",
                         "r = (x, 'abcdef'[1:5:2], (1, 2, 3)[::-1], x[-2:])"], "result"),
    # The function is defined in the operation, so that `global` is in the template.
    "global_statement": ([], ["def f():\n    global g\n    g = 5\n    return g + 1",
                              "r = (f(), g)"], "result"),
}


# ---------------------------------------------------------------------------------------------
# Typing and dataclasses (the modules that the grid imports), with the axes: built-in subclasses
# as values and fields (A1), field dunders that re-enter or raise (A2, A4), `default_factory` and
# `__post_init__` of each kind (A3), the alias caches' eviction (A5).

def _user(name, body):
    return f"class {name}:\n{body}    def __repr__(self):\n        return '{name}()'\n"


TYPING = {
    # typing
    "type_checking": ([], ["import typing", "r = typing.TYPE_CHECKING"], "result"),
    "module_names": ([], ["import typing", "import dataclasses",
                          "r = (typing.__name__, dataclasses.__name__)"], "result"),
    "cast_kinds": (["class I(int):\n    pass\n"],
                   ["from typing import cast", "x = I(3)", "r = (cast(int, 3), cast(str, x) is x, cast('T', [1]))"],
                   "result"),
    "any": ([], ["from typing import Any", "r = (repr(Any), Any == Any)"], "result"),
    "any_isinstance": ([], ["from typing import Any", "r = isinstance(1, Any)"], "raises:TypeError"),
    "forward_ref": ([], ["from typing import ForwardRef", "a = ForwardRef('int')",
                         "r = (repr(a), a == ForwardRef('int'), a == ForwardRef('str'), hash(a) == hash(ForwardRef('int')))"],
                    "result"),
    "optional": ([], ["from typing import Optional, Union",
                      "r = (repr(Optional[int]), Optional[int] == Union[int, None], repr(Union[int, str]), Union[int, int] is int)"],
                 "result"),
    "union_ops": ([], ["from typing import Union",
                       "u = Union[int, str]", "r = (repr(u | None), repr(int | u), u.__args__, u == Union[str, int])"],
                  "result"),
    "union_isinstance": ([], ["from typing import Union", "u = Union[int, str]",
                              "r = (isinstance(1, u), isinstance(1.5, u), isinstance('a', int | str), issubclass(bool, int | str))"],
                         "result"),
    "required_forms": ([], ["from typing import Required, NotRequired, TypeGuard",
                            "r = (repr(Required[int]), repr(NotRequired[str]), repr(TypeGuard[int]))"],
                       "result"),
    "aliases": ([], ["from typing import List, Dict, Set, Tuple",
                     "r = (repr(List[int]), repr(Dict[str, int]), repr(Set[int]), repr(Tuple[int, ...]), List[int] == List[int], List[int] != List[str], List[int].__origin__ is list)"],
                "result"),
    "alias_call": ([], ["from typing import List", "r = List[int]([1, 2])"], "raises:TypeError"),
    "alias_isinstance": ([], ["from typing import List", "r = isinstance([], List[int])"], "raises:TypeError"),
    "alias_attributes": ([], ["from typing import Dict", "d = Dict[str, int]",
                              "r = (d.__args__, d.__origin__, d._name)"], "result"),
    "typeddict": ([], ["from typing import TypedDict",
                       "class TD(TypedDict):\n    a: int\n    b: str",
                       "x = TD(a=1, b='x')",
                       "r = (x, type(x).__name__, sorted(TD.__required_keys__), sorted(TD.__optional_keys__), TD.__total__)"],
                  "result"),
    "typeddict_total_false": ([], ["from typing import TypedDict, Required",
                                   "class TD(TypedDict, total=False):\n    a: Required[int]\n    b: str",
                                   "r = (TD(a=1), sorted(TD.__required_keys__), sorted(TD.__optional_keys__))"],
                              "result"),
    "typeddict_inherit": ([], ["from typing import TypedDict, NotRequired",
                               "class A(TypedDict):\n    a: int",
                               "class B(A):\n    b: NotRequired[str]",
                               "r = (B(a=1, b='x'), sorted(B.__required_keys__), sorted(B.__annotations__))"],
                          "result"),
    "typeddict_isinstance": ([], ["from typing import TypedDict",
                                  "class TD(TypedDict):\n    a: int",
                                  "r = isinstance({}, TD)"], "raises:TypeError"),
    "typeddict_sub_values": (["class I(int):\n    pass\n", "class S(str):\n    pass\n"],
                             ["from typing import TypedDict",
                              "class TD(TypedDict):\n    a: int\n    b: str",
                              "x = TD(a=I(1), b=S('s'))", "r = (type(x['a']).__name__, type(x['b']).__name__, x)"],
                             "result"),
    "namedtuple": ([], ["from typing import NamedTuple",
                        "class P(NamedTuple):\n    x: int\n    y: int = 0",
                        "p = P(1)",
                        "r = (p, p.x, p[1], p._replace(y=5), p._asdict(), p.__getnewargs__(), P._make([3, 4]), P.__match_args__, P._fields, P._field_defaults, tuple(p), p == (1, 0), hash(p) == hash((1, 0)))"],
                   "result"),
    "namedtuple_errors": ([], ["from typing import NamedTuple",
                               "class P(NamedTuple):\n    x: int",
                               "r = []",
                               "for f in (lambda: P(), lambda: P(1, 2), lambda: P(x=1, z=2), lambda: P._make([1, 2]), lambda: P(1)._replace(z=1)):\n    try:\n        f()\n    except Exception as e:\n        r.append((type(e).__name__, str(e)))"],
                          "result"),
    "namedtuple_other_base": ([], ["from typing import NamedTuple",
                                   "class P(NamedTuple, int):\n    x: int"],
                              "raises:TypeError"),
    "namedtuple_sub_fields": (["class I(int):\n    pass\n"],
                              ["from typing import NamedTuple",
                               "class P(NamedTuple):\n    x: int",
                               "p = P(I(2))", "r = (type(p.x).__name__, p, p.x + 1)"], "result"),
    "namedtuple_field_eq_reenters": ([_user("E", "    def __eq__(self, o):\n        ev('E.__eq__')\n        log.append('eq')\n        return True\n    __hash__ = object.__hash__\n")],
                                     ["from typing import NamedTuple", "log = []",
                                      "class P(NamedTuple):\n    x: object",
                                      "e = E()", "r = (P(e) == P(E()), P(e) == P(e), log)"], "result"),
    # dataclasses
    "dataclass_basic": ([], ["from dataclasses import dataclass",
                             "@dataclass\nclass D:\n    a: int\n    b: str = 'x'",
                             "d = D(1)", "r = (d, d == D(1, 'x'), d != D(2), D.__match_args__, D.__doc__)"],
                        "result"),
    "dataclass_order": ([], ["from dataclasses import dataclass",
                             "@dataclass(order=True)\nclass D:\n    a: int\n    b: int = 0",
                             "r = (D(1) < D(2), D(1, 2) > D(1, 1), D(1) <= D(1), D(2) >= D(1), sorted([D(3), D(1), D(2)]))"],
                        "result"),
    "dataclass_order_mixed": ([], ["from dataclasses import dataclass",
                                   "@dataclass(order=True)\nclass D:\n    a: int",
                                   "r = D(1) < 1"], "raises:TypeError"),
    "dataclass_frozen": ([], ["from dataclasses import dataclass, FrozenInstanceError",
                              "@dataclass(frozen=True)\nclass D:\n    a: int",
                              "d = D(1)",
                              "try:\n    d.a = 2\nexcept FrozenInstanceError as e:\n    r = (type(e).__name__, str(e), hash(d) == hash(D(1)), d)"],
                         "result"),
    "dataclass_frozen_del": ([], ["from dataclasses import dataclass, FrozenInstanceError",
                                  "@dataclass(frozen=True)\nclass D:\n    a: int",
                                  "try:\n    del D(1).a\nexcept FrozenInstanceError as e:\n    r = str(e)"],
                             "result"),
    "dataclass_hash_actions": ([], ["from dataclasses import dataclass",
                                    "@dataclass\nclass A:\n    a: int",
                                    "@dataclass(eq=False)\nclass B:\n    a: int",
                                    "@dataclass(unsafe_hash=True)\nclass C:\n    a: int",
                                    "@dataclass(frozen=True, eq=True)\nclass E:\n    a: int",
                                    "r = (A.__hash__, B.__hash__ is object.__hash__, hash(C(1)) == hash((1,)), hash(E(2)) == hash((2,)))"],
                               "result"),
    "dataclass_options": ([], ["from dataclasses import dataclass",
                               "@dataclass(repr=False, init=False, eq=False, match_args=False)\nclass D:\n    a: int = 3",
                               "d = D()", "r = (d.a, D.__repr__ is object.__repr__, hasattr(D, '__match_args__'), d == D())"],
                          "result"),
    "dataclass_kw_only": ([], ["from dataclasses import dataclass, field",
                               "@dataclass(kw_only=True)\nclass D:\n    a: int\n    b: int = field(default=2, kw_only=False)",
                               "r = (D(5, a=1), D.__match_args__)"], "result"),
    "dataclass_kw_only_error": ([], ["from dataclasses import dataclass",
                                     "@dataclass(kw_only=True)\nclass D:\n    a: int",
                                     "r = D(1)"], "raises:TypeError"),
    "dataclass_mutable_default": ([], ["from dataclasses import dataclass",
                                       "@dataclass\nclass D:\n    a: list = []"],
                                  "raises:ValueError"),
    "dataclass_field_order_error": ([], ["from dataclasses import dataclass",
                                         "@dataclass\nclass D:\n    a: int = 1\n    b: int"],
                                    "raises:TypeError"),
    "dataclass_post_init": ([], ["from dataclasses import dataclass, field",
                                 "@dataclass\nclass D:\n    a: int\n    b: int = field(init=False)\n    def __post_init__(self):\n        ev('D.__post_init__')\n        self.b = self.a * 2",
                                 "r = D(3)"], "result"),
    "dataclass_replace": ([], ["from dataclasses import dataclass, replace",
                               "@dataclass(frozen=True)\nclass D:\n    a: int\n    b: int = 0",
                               "d = D(1)", "r = (replace(d, b=5), replace(d), d)"], "result"),
    "dataclass_replace_error": ([], ["from dataclasses import dataclass, replace",
                                     "@dataclass\nclass D:\n    a: int",
                                     "r = replace(D(1), z=2)"], "raises:TypeError"),
    "dataclass_field_object": ([], ["from dataclasses import field, Field, MISSING",
                                    "f = field(default=3)",
                                    "r = (type(f).__name__, isinstance(f, Field), f.default, f.default_factory is MISSING)"],
                               "result"),
    "dataclass_inherit": ([], ["from dataclasses import dataclass",
                               "@dataclass\nclass A:\n    a: int",
                               "@dataclass\nclass B(A):\n    b: int = 0",
                               "r = (B(1), B(1, 2) == B(1, 2), B.__match_args__)"], "result"),
    "dataclass_builtin_sub_fields": (["class I(int):\n    pass\n", "class L(list):\n    pass\n"],
                                     ["from dataclasses import dataclass",
                                      "@dataclass(order=True)\nclass D:\n    a: int\n    b: list",
                                      "x = D(I(1), L([2]))", "r = (x, type(x.a).__name__, x == D(1, [2]), x < D(2, []))"],
                                     "result"),
    "dataclass_on_builtin_sub": ([], ["from dataclasses import dataclass",
                                      "@dataclass\nclass D(list):\n    a: int = 0",
                                      "d = D()", "r = (d, d.a, list.__len__(d))"], "result"),
    "dataclass_field_eq_reenters": ([_user("E", "    def __eq__(self, o):\n        ev('E.__eq__')\n        log.append(len(log))\n        return True\n    __hash__ = object.__hash__\n")],
                                    ["from dataclasses import dataclass", "log = []",
                                     "@dataclass\nclass D:\n    a: object\n    b: object",
                                     "r = (D(E(), 1) == D(E(), 1), D(1, E()) == D(1, E()), log)"], "result"),
    "dataclass_field_eq_raises": ([_user("E", "    def __eq__(self, o):\n        raise ValueError('eq')\n    __hash__ = object.__hash__\n")],
                                  ["from dataclasses import dataclass",
                                   "@dataclass\nclass D:\n    a: object",
                                   "r = D(E()) == D(E())"], "raises:ValueError"),
    "dataclass_field_hash_raises": ([_user("H", "    def __hash__(self):\n        raise ValueError('hash')\n")],
                                    ["from dataclasses import dataclass",
                                     "@dataclass(unsafe_hash=True)\nclass D:\n    a: object",
                                     "r = hash(D(H()))"], "raises:ValueError"),
    "dataclass_field_repr_raises": (["class R:\n    def __repr__(self):\n        ev('R.__repr__')\n        raise KeyError('repr')\n"],
                                    ["from dataclasses import dataclass",
                                     "@dataclass\nclass D:\n    a: object",
                                     "r = repr(D(R()))"], "raises:KeyError"),
    "dataclass_field_lt_notimpl": ([_user("N", "    def __lt__(self, o):\n        ev('N.__lt__')\n        return NotImplemented\n    def __gt__(self, o):\n        ev('N.__gt__')\n        return NotImplemented\n")],
                                   ["from dataclasses import dataclass",
                                    "@dataclass(order=True)\nclass D:\n    a: object",
                                    "r = D(N()) < D(N())"], "raises:TypeError"),
    "dataclass_recursive_repr": ([], ["from dataclasses import dataclass",
                                      "@dataclass\nclass D:\n    a: object = None",
                                      "d = D()", "d.a = d", "r = repr(d)"], "result"),
    "dataclass_eq_other_class": ([], ["from dataclasses import dataclass",
                                      "@dataclass\nclass A:\n    a: int",
                                      "@dataclass\nclass B:\n    a: int",
                                      "r = (A(1) == B(1), A(1) == (1,), A(1).__eq__(B(1)))"], "result"),
    # default_factory and __post_init__ of each kind (A3).
    "factory_function": ([], ["from dataclasses import dataclass, field",
                              "def make():\n    ev('make')\n    return [0]",
                              "@dataclass\nclass D:\n    a: list = field(default_factory=make)",
                              "r = (D(), D().a is not D().a)"], "result"),
    "factory_lambda": ([], ["from dataclasses import dataclass, field",
                            "@dataclass\nclass D:\n    a: dict = field(default_factory=lambda: {'k': 1})",
                            "r = D()"], "result"),
    "factory_builtin": ([], ["from dataclasses import dataclass, field",
                             "@dataclass\nclass D:\n    a: list = field(default_factory=list)\n    b: set = field(default_factory=set)",
                             "r = D()"], "result"),
    "factory_class": ([_user("K", "    def __init__(self):\n        ev('K.__init__')\n")],
                      ["from dataclasses import dataclass, field",
                       "@dataclass\nclass D:\n    a: object = field(default_factory=K)",
                       "r = D()"], "result"),
    "factory_callable_object": ([_user("Mk", "    def __call__(self):\n        ev('Mk.__call__')\n        return 7\n")],
                                ["from dataclasses import dataclass, field",
                                 "@dataclass\nclass D:\n    a: int = field(default_factory=Mk())",
                                 "r = D()"], "result"),
    "factory_raises": ([], ["from dataclasses import dataclass, field",
                            "def make():\n    raise ValueError('factory')",
                            "@dataclass\nclass D:\n    a: int = field(default_factory=make)",
                            "r = D()"], "raises:ValueError"),
    "post_init_staticmethod": ([], ["from dataclasses import dataclass",
                                    "@dataclass\nclass D:\n    a: int\n    @staticmethod\n    def __post_init__():\n        ev('D.__post_init__')",
                                    "r = D(1)"], "result"),
    "post_init_classmethod": ([], ["from dataclasses import dataclass",
                                   "@dataclass\nclass D:\n    a: int\n    @classmethod\n    def __post_init__(cls):\n        ev('D.__post_init__')",
                                   "r = D(1)"], "result"),
    "post_init_raises": ([], ["from dataclasses import dataclass",
                              "@dataclass\nclass D:\n    a: int\n    def __post_init__(self):\n        raise KeyError(self.a)",
                              "r = D(1)"], "raises:KeyError"),
    # types: GenericAlias and UnionType
    "generic_alias": ([], ["r = (repr(list[int]), list[int] == list[int], list[int].__origin__ is list, list[int].__args__, repr(dict[str, list[int]]), repr(type[int]))"],
                      "result"),
    "union_type": ([], ["u = int | str", "r = (repr(u), type(u).__name__, u.__args__, int | int, repr(int | None), isinstance(1, u), u == (str | int))"],
                   "result"),
    "union_type_errors": ([], ["r = []",
                               "for f in (lambda: int | 1, lambda: isinstance(1, list[int]), lambda: list[int](1)):\n    try:\n        r.append(f())\n    except Exception as e:\n        r.append(type(e).__name__)"],
                          "result"),
}

def module_reads(op, cid):
    """The attributes of `typing` and `dataclasses` that the operation reads: each name of a
    `from <module> import …` and each `<module>.<name>`. A name that a `from … import` brings in
    must be used in the operation, or the declared read would be no evidence."""
    names = []
    text = "\n".join(op)
    for mod in ("typing", "dataclasses"):
        for m in re.finditer(rf"from {mod} import ([\w, ]+)", text):
            for n in (x.strip() for x in m.group(1).split(",")):
                rest = text[:m.start()] + text[m.end():]
                if not re.search(rf"\b{n}\b", rest):
                    raise ValueError(f"{cid}: imports {mod}.{n} but doesn't use it")
                names.append(f"{mod}.{n}")
        names += [f"{mod}.{n}" for n in re.findall(rf"\b{mod}\.(\w+)", text)]
    return sorted(set(names))


# The axis of each case of `TYPING`: A1 for the kinds of value, A2 to A4 as in the grid, and
# `plain` for a case of exact built-in values.
TYPING_AXES = {
    "cast_kinds": "A1", "typeddict_sub_values": "A1", "namedtuple_sub_fields": "A1",
    "dataclass_builtin_sub_fields": "A1", "dataclass_on_builtin_sub": "A1",
    "namedtuple_field_eq_reenters": "A2", "dataclass_field_eq_reenters": "A2",
    "dataclass_recursive_repr": "A2",
    "dataclass_field_eq_raises": "A4", "dataclass_field_hash_raises": "A4",
    "dataclass_field_repr_raises": "A4", "dataclass_field_lt_notimpl": "A4",
    "factory_raises": "A4", "post_init_raises": "A4",
    "factory_function": "A3", "factory_lambda": "A3", "factory_builtin": "A3",
    "factory_class": "A3", "factory_callable_object": "A3", "post_init_staticmethod": "A3",
    "post_init_classmethod": "A3", "dataclass_post_init": "A3",
}

TYPING_DIR = pathlib.Path(__file__).resolve().parent / "typing"


def typing_file_cases():
    """The cases of `typing/<axis>_<name>.py`: each file is a whole operation. A line
    `# expect: <outcome>` gives its expected outcome (default `result`), and a line
    `# entries: <key>, …` the natives of the C types (`types.GenericAlias`, `types.UnionType`,
    `collections._tuplegetter`) that its operation reaches without a call."""
    cases = []
    for f in sorted(TYPING_DIR.glob("*.py")):
        axis, _, name = f.stem.partition("_")
        text = f.read_text()
        expect = "result"
        entries = []
        for line in text.splitlines():
            if line.startswith("# expect: "):
                expect = line[len("# expect: "):].strip()
            if line.startswith("# entries: "):
                entries = [e.strip() for e in line[len("# entries: "):].split(",")]
        op = text.rstrip("\n").split("\n") + ["r = None"]
        cid = f"tf_{f.stem}"
        cases.append(Case(cid, "typing", axis, name, name, op, [], [], expect,
                          reads=module_reads(op, cid) + entries))
    return cases


def typing_cases():
    cases = table_cases("t", "typing", "typing", TYPING)
    for c in cases:
        c.axis = TYPING_AXES.get(c.kind, "plain")
        c.reads = module_reads(c.op, c.id)
    return cases + typing_file_cases()


def regression_cases():
    return table_cases("reg", "regressions", "regression", REGRESSIONS)


def all_cases():
    cases = (a1_cases() + method_cases() + a3_cases() + a4_cases()
             + table_cases("a2", "reentry", "A2", A2)
             + table_cases("a5", "limits", "A5", A5)
             + table_cases("a6", "iteration", "A6", A6)
             + a7_cases() + table_cases("fast", "fast-paths", "fast", FAST)
             + table_cases("res", "results", "A1", RESULTS)
             + direct_cases()
             + constructor_cases()
             + table_cases("call", "calls", "direct", CALLS, CALLS_CALLS, CALLS_ENTRIES)
             + table_cases("syn", "syntax", "syntax", SYNTAX)
             + typing_cases()
             + regression_cases())
    seen = set()
    for c in cases:
        if c.id in seen:
            raise ValueError(f"duplicate case id {c.id}")
        seen.add(c.id)
    return cases
