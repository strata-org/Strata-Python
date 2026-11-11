# list[int] and the other built-in generic aliases, and type[int].
a = list[int]
b = list[int]
print(a, dict[str, int], tuple[()], tuple[int, ...], set[int], frozenset[str], type[int])
print(a == b, a is b, a == list[str], a != list[str], a == 1, a.__hash__)
print(a.__origin__, a.__args__, a.__parameters__, a.__unpacked__, list[1], list[list[int]])
print(a.append is list.append, a.__mro_entries__(()), a.__class__ is type(a))
print(type(a).__name__, type(a).__qualname__)
print(dict[[int], str], list[...])
class C:
    pass
try:
    C[int]
except TypeError as e:
    print("TypeError:", e)
try:
    isinstance([], list[int])
except TypeError as e:
    print("TypeError:", e)
try:
    list[int][int]
except TypeError as e:
    print("TypeError:", e)
try:
    type(a).x = 1
except TypeError as e:
    print("TypeError:", e)
d = {list[int]: 1}
print(d[list[int]])
print(type[int](3))
print(type(a).__module__)
# Calling the alias calls list, the library's.
print(a(), a(range(3)), type(a()))
