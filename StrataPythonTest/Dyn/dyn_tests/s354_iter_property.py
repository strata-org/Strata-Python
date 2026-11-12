# A class whose __iter__ is a property: CPython binds it first, as lookup_maybe_method does, and
# calls the bound value. A getter that gives None, or that raises, makes the object not iterable.
class A:
    __iter__ = property(lambda self: None)
class B:
    @property
    def __iter__(self):
        raise KeyError("k")
class D:
    __iter__ = property(lambda self: lambda: iter([7, 8]))
for c in [A, B]:
    try:
        for x in c():
            print(x)
    except TypeError as e:
        print("TypeError", e)
for x in D():
    print(x)
