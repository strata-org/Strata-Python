# The repr of an alias looks at its origin first, then at its arguments in order.
class D:
    def __get__(self, obj, owner):
        print("get", owner.__name__)
        raise AttributeError("x")
class L(list):
    __origin__ = D()
class B:
    __origin__ = D()
class E:
    __origin__ = D()
print(repr(L[B, E]))
