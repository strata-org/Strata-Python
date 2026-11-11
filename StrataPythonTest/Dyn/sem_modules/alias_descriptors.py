# The methods of types.GenericAlias and types.UnionType as descriptors.
GA = type(list[int])
U = type(int | str)
print(type(GA.__eq__).__name__, type(GA.__mro_entries__).__name__)
print(type((int | str).__eq__).__name__, type(list[int].__mro_entries__).__name__)
print(GA.__eq__(list[int], 1), GA.__ror__(list[int], "x"), GA.__eq__(list[int], list[int]))
for f in [lambda: GA.__eq__(int | str, 1), lambda: GA.__mro_entries__(int | str, ()),
          lambda: U.__repr__(list[int]),
          lambda: GA.__eq__(), lambda: GA.__mro_entries__(), lambda: list.__class_getitem__(),
          lambda: list[int].__mro_entries__(), lambda: GA.__instancecheck__(list[int])]:
    try:
        f()
    except TypeError as e:
        print("TypeError:", e)
try:
    class T(U):
        pass
except TypeError as e:
    print("TypeError:", e)
# Binding by hand checks the receiver too.
try:
    GA.__eq__.__get__(int | str)
except TypeError as e:
    print("TypeError:", e)
