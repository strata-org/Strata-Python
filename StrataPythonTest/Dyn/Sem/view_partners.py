"""For a sample of built-in types, call every binary and comparison dunder that the type's MRO
gives with a dict_keys view. Print `SAMPLED TYPE` for each sample, and `TYPE DUNDER` for each
dunder that doesn't give NotImplemented, with the sample's own type name (`type(s).__name__`),
so that a sample under the wrong label can't stand for another type. StrataPythonTestExtra/ViewPartnersTest.lean checks that
every built-in type of the semantics that can meet a view at trySlot has a sample, and which of
its dunders may not give NotImplemented.

Run it with CPython 3.12:
    python3.12 -I StrataPythonTest/Dyn/Sem/view_partners.py
"""
import builtins
import types


class K:
    x = 1

    def m(self):
        pass


def f():
    pass


def cell():
    x = 1
    return (lambda: x).__closure__[0]


samples = {
    "NoneType": None, "NotImplementedType": NotImplemented, "ellipsis": ..., "bool": True,
    "int": 1, "float": 1.0, "complex": 1j, "str": "a", "bytes": b"a", "bytearray": bytearray(b"a"),
    "memoryview": memoryview(b"a"), "tuple": (1,), "range": range(2), "slice": slice(1),
    "list": [1], "dict": {1: 0}, "set": {1}, "frozenset": frozenset({1}), "object": object(),
    "type": int, "function": f, "builtin_function_or_method": len, "method": K().m,
    "method-wrapper": (1).__add__, "wrapper_descriptor": object.__eq__,
    "method_descriptor": str.join, "classmethod_descriptor": dict.__dict__["fromkeys"],
    "getset_descriptor": type.__dict__["__name__"], "member_descriptor": slice.__dict__["start"],
    "mappingproxy": K.__dict__, "module": builtins, "cell": cell(), "property": property(),
    "classmethod": classmethod(f), "staticmethod": staticmethod(f), "super": super(int, 1),
    "zip": zip(), "enumerate": enumerate([]), "reversed": reversed([]), "filter": filter(None, []),
    "map": map(f, []), "list_iterator": iter([]), "tuple_iterator": iter(()),
    "str_ascii_iterator": iter("a"), "str_iterator": iter("é"), "bytes_iterator": iter(b""),
    "range_iterator": iter(range(1)), "longrange_iterator": iter(range(2 ** 64)),
    "dict_keyiterator": iter({}), "dict_valueiterator": iter({}.values()),
    "dict_itemiterator": iter({}.items()), "list_reverseiterator": reversed([]),
    "dict_reversekeyiterator": reversed({}), "dict_reversevalueiterator": reversed({}.values()),
    "dict_reverseitemiterator": reversed({}.items()), "set_iterator": iter(set()),
    "callable_iterator": iter(f, 1), "iterator": iter(type("G", (), {"__getitem__": lambda s, i: 1})()),
    "dict_keys": {}.keys(), "dict_values": {}.values(), "dict_items": {}.items(),
    "ModuleSpec": builtins.__spec__, "Quitter": builtins.exit,
    "_Helper": builtins.help, "_Printer": builtins.copyright,
    "BuiltinImporter": builtins.__loader__, "ExceptionGroup": ExceptionGroup("x", [ValueError()]),
    "BaseExceptionGroup": BaseExceptionGroup("x", [KeyboardInterrupt()]),
    "UnicodeDecodeError": UnicodeDecodeError("utf-8", b"a", 0, 1, "x"),
    "UnicodeEncodeError": UnicodeEncodeError("utf-8", "a", 0, 1, "x"),
    "UnicodeTranslateError": UnicodeTranslateError("a", 0, 1, "x"),
}
try:
    raise ValueError
except ValueError as e:
    samples["traceback"] = e.__traceback__
for name in dir(builtins):
    c = getattr(builtins, name)
    if isinstance(c, type) and issubclass(c, BaseException) and name not in samples:
        try:
            samples[name] = c()
        except TypeError:
            pass

names = ["__add__", "__radd__", "__sub__", "__rsub__", "__mul__", "__rmul__", "__truediv__",
         "__rtruediv__", "__floordiv__", "__rfloordiv__", "__mod__", "__rmod__", "__pow__",
         "__rpow__", "__lshift__", "__rlshift__", "__rshift__", "__rrshift__", "__and__",
         "__rand__", "__or__", "__ror__", "__xor__", "__rxor__", "__matmul__", "__rmatmul__",
         "__divmod__", "__rdivmod__", "__eq__", "__ne__", "__lt__", "__le__", "__gt__", "__ge__"]
for s in samples.values():
    t = type(s)
    tname = t.__name__
    print("SAMPLED", tname)
    for n in names:
        fn = next((c.__dict__[n] for c in t.__mro__ if n in c.__dict__), None)
        if fn is None:
            continue
        try:
            r = fn(s, {1: 0}.keys())
        except Exception:
            print(tname, n)
            continue
        if r is not NotImplemented:
            print(tname, n)
