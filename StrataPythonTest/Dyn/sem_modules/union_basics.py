# int | None and the other unions of types.
u = int | None
print(u, int | str | None, None | int, int | int, list[int] | None, None | type(None))
print(u == (None | int), (int | str) == (str | int), u != (int | str), u == 1, u.__args__, u.__parameters__)
print((int | str).__args__, type(u).__name__)
print(list[int] | list[int], int | list[int] | list[int], (int | str) | (str | int))
print(isinstance(1, int | str), isinstance("x", int | str), isinstance(1.0, int | str))
print(isinstance(1, int | list[int]))
try:
    isinstance([], list[int] | int)
except TypeError as e:
    print("TypeError:", e)
try:
    int | "x"
except TypeError as e:
    print("TypeError:", e)
try:
    (int | str)[int]
except TypeError as e:
    print("TypeError:", e)
d = {int | str: 1}
print(d[str | int])
print(type(u).__module__)
print(issubclass(bool, int | str), issubclass(bool, (str, int | None)), issubclass(float, int | str))
