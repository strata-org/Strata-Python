g = list[int]
u = int | str
for f in (lambda: g != list[str], lambda: g < g, lambda: issubclass(list, g), lambda: u != (int | None), lambda: u < u, lambda: list[int]([1, 2]), lambda: issubclass(bool, u), lambda: None | int):
    try:
        print(f())
    except Exception as e:
        print(type(e).__name__, e)
class C(list[int]):
    pass
print(C.__bases__, C.__orig_bases__ == (list[int],))
