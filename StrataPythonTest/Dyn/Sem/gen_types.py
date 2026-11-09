#!/usr/bin/env python3
"""Write the built-in constants of the Python semantics, as CPython 3.12 has them.

Writes `StrataPython/Dyn/Sem/Generated/Types.lean`: the inductive `Builtin`, with one
constructor per object that a name of `dir(builtins)` is bound to, other than an immediate of
`Value` (an alias such as `IOError` names `OSError`'s constructor), and one per built-in type that
a value of the semantics can have; and for each constructor its kind (a type, a built-in function, or
another object), its `__name__`, `__qualname__`, `__module__`, its C `tp_name` (the name that
CPython's messages use), what its hash depends on, and, for a type, its bases, its MRO and its
solid base (CPython's `solid_base`, which decides whether two bases have conflicting instance
layouts).

The types outside `builtins` are found by applying `type()` to a sample of every kind of value
that the rules make (`SAMPLES` below), so the list follows CPython's own choice of type, such as
`str_ascii_iterator` for an ASCII `str` and `longrange_iterator` for a range beyond C long bounds.

Run it with CPython 3.12, from the package root:

    python3.12 StrataPythonTest/Dyn/Sem/gen_types.py

Any other version is refused: the names, the bases and the layouts are 3.12's.
"""

import builtins
import ctypes
import sys
import types
from pathlib import Path

if sys.version_info[:2] != (3, 12):
    sys.exit(f"gen_types.py needs CPython 3.12, not {sys.version.split()[0]}")

OUT = Path(__file__).resolve().parents[3] / "StrataPython/Dyn/Sem/Generated/Types.lean"


def _cell():
    x = 0

    def f():
        return x
    return f.__closure__[0]


class _GetItem:
    """A class with `__getitem__` and no `__iter__`: `iter()` of an instance is CPython's
    `iterator` type."""

    def __getitem__(self, i):
        raise IndexError


class _Slotted:
    __slots__ = ("x",)

    def f(self):
        return 0


def _samples():
    """Values of every kind that the rules make, for `type()`."""
    d = {1: 2}
    out = [
        iter([]), iter(()), iter(""), iter("é"), iter(b""), iter(range(1)),
        iter(range(2**70)), iter(d), iter(d.values()), iter(d.items()), reversed([]),
        reversed(d), reversed(d.values()), reversed(d.items()), iter(set()), zip(),
        enumerate([]), reversed(range(1)), reversed(range(2**70)), reversed(()),
        iter(lambda: 0, 1), iter(_GetItem()), d.keys(), d.values(), d.items(), None, NotImplemented, ...,
        lambda: 0, [].append, len, str.upper, int.__add__, (1).__add__,
        dict.__dict__["fromkeys"], type.__dict__["__name__"], _Slotted.__dict__["x"],
        type.__dict__, builtins, list[int], int | str, property(), classmethod(len),
        staticmethod(len), super(int, 1), (1).__index__, _Slotted().f, _cell(),
        builtins.exit, builtins.help, builtins.copyright, builtins.__spec__,
    ]
    try:
        raise ValueError
    except ValueError as e:
        out.append(e.__traceback__)
    out.append(object().__init__)  # a method-wrapper
    return out


# Names of `dir(builtins)` whose value is an immediate of `Value` (`None`, `True`, `False`,
# `Ellipsis`, `NotImplemented`, `__debug__`, and the strs `__doc__`, `__name__`, `__package__`):
# they are not `Builtin` constants.  `Builtin.strNames` records the three strs' values.
IMMEDIATE_NAMES = {"None", "True", "False", "Ellipsis", "NotImplemented", "__debug__",
                   "__doc__", "__name__", "__package__"}


def tp_name(t):
    """The C `tp_name` of type `t`: a `const char *` after the object header and `ob_size`."""
    ptr = ctypes.c_char_p.from_address(id(t) + 3 * ctypes.sizeof(ctypes.c_void_p))
    return ptr.value.decode()


def solid_base(t):
    """CPython 3.12's `solid_base`: the nearest type in `t`'s base chain whose instances have a
    shape of their own (`shape_differs`)."""
    base = solid_base(t.__base__) if t.__base__ is not None else object
    if t is object:
        return object
    if t.__basicsize__ != base.__basicsize__ or t.__itemsize__ != base.__itemsize__:
        return t
    return base


def hash_kind(obj):
    """What `hash(obj)` depends on: the object's address, nothing (unhashable), or something else
    (a built-in function hashes its `__self__` and its C function)."""
    try:
        h = hash(obj)
    except TypeError:
        return "unhashable"
    return "addr" if h == object.__hash__(obj) else "other"


def lean_ident(name):
    return f"«{name}»"


def lean_str(s):
    out = s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\t", "\\t")
    return '"' + out + '"'


def collect():
    """The constants: `(key, kind, obj)`, `key` the constructor's name."""
    entries = {}
    order = []

    def add(key, kind, obj):
        if key in entries:
            return
        entries[key] = (kind, obj)
        order.append(key)

    for name in dir(builtins):
        if name in IMMEDIATE_NAMES:
            continue
        obj = getattr(builtins, name)
        if isinstance(obj, type):
            # An alias such as `IOError` is the same object as `OSError`: one constant, named
            # by the type's own `__name__`; `Builtin.ofName?` maps the alias to it.
            add(obj.__name__, "type", obj)
        elif isinstance(obj, types.BuiltinFunctionType):
            add(name, "function", obj)
        else:
            add(name, "other", obj)

    pending = [type(v) for v in _samples()]
    while pending:
        t = pending.pop(0)
        for b in t.__mro__:
            key = b.__name__ if b.__module__ == "builtins" else f"{b.__module__}.{b.__qualname__}"
            if b.__module__ == "builtins" and key in entries and entries[key][1] is not b:
                key = f"builtins.{b.__qualname__}"
            add(key, "type", b)
    return order, entries


def key_of(entries, t):
    for k, (kind, obj) in entries.items():
        if kind == "type" and obj is t:
            return k
    raise KeyError(f"type {t!r} has no constant")


def main():
    order, entries = collect()
    lines = [
        "/-",
        "  Copyright Strata Contributors",
        "",
        "  SPDX-License-Identifier: Apache-2.0 OR MIT",
        "-/",
        "module",
        "",
        "set_option autoImplicit false",
        "",
        "/-!",
        "# Built-in constants (generated)",
        "",
        f"Generated by `StrataPythonTest/Dyn/Sem/gen_types.py` from CPython {sys.version.split()[0]}.",
        "Do not edit: run the script again.",
        "",
        "`Builtin` has one constructor per object that a name of `dir(builtins)` is bound to, other than",
        "an immediate (an alias such as `IOError` names the constant of `OSError`), and one per built-in",
        "type that a value of the semantics can have.  `Builtin.info` gives each",
        "one's kind, names, C `tp_name`, what its hash depends on, and for a type its bases, MRO and",
        "solid base.",
        "-/",
        "",
        "namespace StrataPython.Dyn.Sem",
        "",
        "/-- What the hash of a built-in constant depends on. -/",
        "public inductive BuiltinHash where",
        "  /-- Its address, as `object.__hash__` gives. -/",
        "  | addr",
        "  /-- Nothing: `hash()` raises `TypeError`. -/",
        "  | unhashable",
        "  /-- Two addresses combined: a built-in function's hash, from its `__self__` and its C",
        "  function. -/",
        "  | other",
        "  deriving DecidableEq, Repr, Inhabited",
        "",
        "/-- What a built-in constant is. -/",
        "public inductive BuiltinKind where",
        "  | type | function | other",
        "  deriving DecidableEq, Repr, Inhabited",
        "",
        "/-- A built-in function, type, or other built-in object of CPython 3.12. -/",
        "public inductive Builtin where",
    ]
    for k in order:
        lines.append(f"  | {lean_ident(k)}")
    lines += [
        "  deriving DecidableEq, Repr, Inhabited, Ord",
        "",
        "/-- A built-in constant's hash, by its constructor; written by hand, so that its body is exposed. -/",
        "public instance : Hashable Builtin := ⟨fun b => hash b.ctorIdx⟩",
        "",
        "/-- A built-in constant's data, as CPython 3.12 has it. -/",
        "public structure BuiltinInfo where",
        "  kind : BuiltinKind",
        "  name : String",
        "  qualname : String",
        "  module : String",
        "  /-- The C `tp_name` of a type, which CPython's messages use; empty for a non-type. -/",
        "  tpName : String",
        "  bases : Array Builtin",
        "  mro : Array Builtin",
        "  /-- CPython's `solid_base`, for a type; the constant itself otherwise. -/",
        "  solidBase : Builtin",
        "  /-- The `__itemsize__` of a type (nonzero for a variable-size one such as `int`); 0 otherwise. -/",
        "  itemsize : Nat",
        "  /-- Whether a class may derive from the type (CPython's `Py_TPFLAGS_BASETYPE`). -/",
        "  basetype : Bool",
        "  /-- Whether the instances of a type have a `__dict__` (CPython's `tp_dictoffset != 0`). -/",
        "  instanceDict : Bool",
        "  hash : BuiltinHash",
        "",
        "@[expose] public section",
        "",
        "/-- The data of each built-in constant. -/",
        "def Builtin.info : Builtin → BuiltinInfo",
    ]
    for k in order:
        kind, obj = entries[k]
        if kind == "type":
            name, qual, mod = obj.__name__, obj.__qualname__, obj.__module__
            tpn = tp_name(obj)
            bases = [key_of(entries, b) for b in obj.__bases__]
            mro = [key_of(entries, b) for b in obj.__mro__]
            solid = key_of(entries, solid_base(obj))
            itemsize = obj.__itemsize__
            basetype = bool(obj.__flags__ & (1 << 10))
            instdict = obj.__dictoffset__ != 0
        else:
            name = getattr(obj, "__name__", k) if kind == "function" else k
            qual = getattr(obj, "__qualname__", name) if kind == "function" else k
            mod = "builtins"
            tpn, bases, mro, solid, itemsize, basetype = "", [], [], k, 0, False
            instdict = False
        arr = lambda xs: "#[" + ", ".join(f".{lean_ident(x)}" for x in xs) + "]"
        lines.append(
            f"  | .{lean_ident(k)} => ⟨.{kind}, {lean_str(name)}, {lean_str(qual)}, "
            f"{lean_str(mod)}, {lean_str(tpn)}, {arr(bases)}, {arr(mro)}, .{lean_ident(solid)}, "
            f"{itemsize}, {'true' if basetype else 'false'}, {'true' if instdict else 'false'}, "
            f".{hash_kind(obj)}⟩"
        )
    lines += [
        "",
        "/-- The type of each built-in constant, `type(x)`. -/",
        "def Builtin.typeOf : Builtin → Builtin",
    ]
    for k in order:
        kind, obj = entries[k]
        lines.append(f"  | .{lean_ident(k)} => .{lean_ident(key_of(entries, type(obj)))}")
    lines += [
        "",
        "/-- Every built-in constant, in `dir(builtins)`'s order, then the other types. -/",
        "def Builtin.allConstants : Array Builtin := #[" + ", ".join(f".{lean_ident(k)}" for k in order) + "]",
        "",
        "/-- The constant that the name `name` of the `builtins` module is bound to, if any. -/",
        "def Builtin.ofName? : String → Option Builtin",
    ]
    for name in dir(builtins):
        if name in IMMEDIATE_NAMES:
            continue
        obj = getattr(builtins, name)
        key = obj.__name__ if isinstance(obj, type) else name
        lines.append(f"  | {lean_str(name)} => some .{lean_ident(key)}")
    lines += [
        "  | _ => none",
        "",
        "/-- Every name of the `builtins` module's dict, in the dict's order (`list(vars(builtins))`). -/",
        "def Builtin.dictNames : Array String := #[" + ", ".join(lean_str(n) for n in vars(builtins)) + "]",
        "",
        "/-- The names of `dir(builtins)` bound to a `str`, with their values. -/",
        "def Builtin.strNames : List (String × String) := [" + ", ".join(
            f"({lean_str(n)}, {lean_str(getattr(builtins, n))})"
            for n in sorted(IMMEDIATE_NAMES) if isinstance(getattr(builtins, n), str)) + "]",
        "",
        "end",
        "",
        "end StrataPython.Dyn.Sem",
        "",
    ]
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text("\n".join(lines))
    print(f"wrote {OUT} ({len(order)} constants)")


if __name__ == "__main__":
    main()
