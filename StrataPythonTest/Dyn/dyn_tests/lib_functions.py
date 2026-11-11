# getattr, hasattr, setattr, callable, issubclass, hash, abs, divmod and hex.
class A:
    x = 1


class G:
    def __getattr__(self, name):
        if name == "boom":
            raise ValueError("boom")
        return 7


class Meta(type):
    def __subclasscheck__(cls, sub):
        print("check", sub.__name__)
        return True


class M(metaclass=Meta):
    pass


class B:
    pass


class C:
    def __call__(self):
        return 1


class I(int):
    pass


class F(float):
    pass


class D:
    def __divmod__(self, other):
        return ("divmod", other)

    def __rdivmod__(self, other):
        return ("rdivmod", other)


class Idx:
    def __index__(self):
        return 255


def errors(f, *args, **kwargs):
    try:
        f(*args, **kwargs)
    except (TypeError, ValueError, ZeroDivisionError, AttributeError, OverflowError) as e:
        print(type(e).__name__, e.args[0])


a = A()
print(getattr(a, "x"), getattr(a, "y", 5), hasattr(a, "x"), hasattr(a, "y"))
errors(getattr, a, "y")
g = G()
print(getattr(g, "y"), hasattr(g, "y"))
errors(getattr, g, "boom", 0)
errors(hasattr, g, "boom")
errors(getattr, a, 1)
errors(hasattr, a, 1)
errors(getattr, a)
errors(getattr, a, "x", 1, 2)
errors(getattr, a, "x", default=1)
setattr(a, "z", 3)
print(a.z, setattr(a, "w", 4) is None)
errors(setattr, a, 2, 3)
errors(setattr, 1, "x", 3)
print(callable(len), callable(A), callable(a), callable(C()), callable(1), callable(A.__init__), callable(print))
errors(callable)
print(issubclass(bool, int), issubclass(int, bool), issubclass(B, (int, object)), issubclass(B, M))
errors(issubclass, 1, int)
errors(issubclass, int, 1)
errors(issubclass, int)
print(hash(1), hash(-1), hash(True), hash(1.0), hash(2.5), hash(()), hash((1, 2)), hash(None) == hash(None))
errors(hash, [])
errors(hash)
print(abs(-3), abs(2.5), abs(-0.0), abs(True), (-3).__abs__())
errors(abs, "a")
print(divmod(7, 2), divmod(-7, 2), divmod(7.5, 2), divmod(True, 2))
print(divmod(D(), 1), divmod(1, D()), divmod(-7.0, 2), divmod(7, -2.0))
errors(divmod, 1, 0)
errors(divmod, 1.0, 0)
errors(divmod, "a", 1)
errors(divmod, 1)
print(hex(255), hex(-255), hex(0), hex(Idx()), hex(True))
errors(hex, 1.5)
print(int.__divmod__(7, 2), int.__rdivmod__(2, 7), float.__divmod__(7.0, 2), int.__divmod__(7, 2.0))
print((5).__int__(), (5).__float__(), (5).__trunc__(), (True).__int__(), type((True).__int__()).__name__)
print((2.7).__int__(), (-2.7).__trunc__(), (1.5).__float__(), (1.5).__abs__())
inf = 1e308 * 10
errors(float.__int__, inf)
errors(float.__int__, inf - inf)
errors(int.__float__, 10 ** 400)
# The subclasses of int and float need their constructors.
print(hash(I(5)), abs(I(-3)), I(-3).__abs__(), divmod(I(7), 2), hex(I(16)))
print(I(5).__int__(), type(I(5).__int__()).__name__, F(1.5).__float__(), type(F(1.5).__float__()).__name__)
