# The natives of the C types `types.GenericAlias`, `types.UnionType` and
# `collections._tuplegetter`, each reached by the operation that CPython runs it for. CPython shows
# no call for them, so the case declares them.
# entries: types.GenericAlias.__repr__, types.GenericAlias.__call__, types.GenericAlias.__getattribute__, types.GenericAlias.__lt__, types.GenericAlias.__le__, types.GenericAlias.__eq__, types.GenericAlias.__ne__, types.GenericAlias.__gt__, types.GenericAlias.__ge__, types.GenericAlias.__or__, types.GenericAlias.__ror__, types.GenericAlias.__mro_entries__, types.GenericAlias.__instancecheck__, types.GenericAlias.__subclasscheck__, types.UnionType.__repr__, types.UnionType.__getattribute__, types.UnionType.__lt__, types.UnionType.__le__, types.UnionType.__eq__, types.UnionType.__ne__, types.UnionType.__gt__, types.UnionType.__ge__, types.UnionType.__or__, types.UnionType.__ror__, collections._tuplegetter.__get__, collections._tuplegetter.__repr__
from typing import NamedTuple
g = list[int]
u = int | str
out = []
for name, f in (("repr", lambda: (repr(g), repr(u))),
                ("call", lambda: g([1, 2])),
                ("attr", lambda: (g.__origin__, g.__args__, u.__args__)),
                ("compare", lambda: (g == list[int], g != list[str], u == (str | int), u != (int | None))),
                ("order", lambda: (g < g)),
                ("order_le", lambda: (g <= g)), ("order_gt", lambda: (g > g)), ("order_ge", lambda: (g >= g)),
                ("union_order", lambda: (u < u)), ("union_le", lambda: (u <= u)),
                ("union_gt", lambda: (u > u)), ("union_ge", lambda: (u >= u)),
                ("or", lambda: (repr(g | None), repr(None | g), repr(u | None), repr(None | u))),
                ("mro_entries", lambda: g.__mro_entries__((g,))),
                ("instancecheck", lambda: isinstance([], g)),
                ("subclasscheck", lambda: issubclass(list, g))):
    try:
        out.append((name, f()))
    except Exception as e:
        out.append((name, type(e).__name__, str(e)))
for o in out:
    print(o)
class P(NamedTuple):
    x: int
p = P(1)
print(p.x, type(P.x).__name__, repr(P.x))
