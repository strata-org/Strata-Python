# The methods of types.GenericAlias and types.UnionType check their receiver before their
# arguments, as CPython's descriptors do.
GA = type(list[int])
U = type(int | str)
for f in [lambda: GA.__eq__(1), lambda: GA.__mro_entries__(1), lambda: GA.__getattribute__(1, 2),
          lambda: U.__or__(1), lambda: GA.__getitem__(1), lambda: GA.__repr__(1, 2),
          lambda: U.__repr__(1, 2), lambda: GA.__getitem__(int | str, int),
          lambda: U.__getitem__(list[int], int), lambda: GA.__hash__(1, 2)]:
    try:
        f()
    except TypeError as e:
        print("TypeError:", e)
