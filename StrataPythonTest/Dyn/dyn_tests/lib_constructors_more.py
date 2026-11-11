# Constructor and function cases from review: CPython's fast paths, keyword rules and call order.
class D(dict):
    def keys(self):
        print("keys")
        return ["a", "b"]

    def __getitem__(self, k):
        print("gi", k)
        return 0


class F(float):
    def __init__(self, x, tag=None):
        self.tag = tag


class T(tuple):
    def __init__(self, it, tag=None):
        self.tag = tag


class FS(frozenset):
    def __init__(self, it, tag=None):
        self.tag = tag


class L(list):
    def __new__(cls, *args, **kwargs):
        return super().__new__(cls)


class S(set):
    pass


class TT(tuple):
    pass


class Grow:
    def __init__(self):
        self.ks = [1, 2]

    def keys(self):
        return self.ks

    def __getitem__(self, k):
        if k == 1:
            self.ks[len(self.ks):] = [3]
        return k * 10


class P:
    def __iter__(self):
        print("iter")
        return PI()


class PI:
    def __init__(self):
        self.i = 0

    def __iter__(self):
        print("iter")
        return self

    def __next__(self):
        self.i += 1
        if self.i > 2:
            raise StopIteration
        return self.i


class NegHint:
    def __iter__(self):
        return self

    def __next__(self):
        raise StopIteration

    def __length_hint__(self):
        return -1


class BS(bytes):
    pass


class X:
    def __bytes__(self):
        return BS(b"x")


def errors(f, *args, **kwargs):
    try:
        f(*args, **kwargs)
    except (TypeError, ValueError, OverflowError) as e:
        print(type(e).__name__, e.args[0])


d = dict(D(a=1))
print(len(d), d["a"])
f = F(1.5, tag=2)
print(f, f.tag)
t = T([1], tag=3)
print(len(t), t.tag)
fs = FS([1], tag=4)
print(len(fs), fs.tag)
print(len(L([1, 2], tag=5)))
errors(S, [1], [2])
errors(FS, [1], [2], [3])
errors(frozenset, [1], x=1)
print(issubclass(int, TT((int,))), issubclass(bool, TT((str, int))))
print(callable(int.real), callable(slice.start), callable(str.upper), callable(dict.fromkeys))
g = dict(Grow())
print(len(g), g[3])
d = dict([P()])
print(d[1])
errors(dict, [NegHint()])
print(type(bytes(X())).__name__, bytes(X()))
errors(bytes, -10 ** 30)
errors(str, encoding=5)
errors(str, errors=5)


class L0(list):
    pass


class Lm(list):
    __new__ = list.__new__


class F0(float):
    pass


class T0(tuple):
    pass


class FS0(frozenset):
    pass


errors(L0, [1], tag=5)
errors(Lm, [1], tag=5)
errors(F0, 1.5, tag=5)
errors(T0, [1], tag=5)
errors(FS0, [1], tag=5)


class Idx:
    def __index__(self):
        return 10 ** 30


class I(int):
    pass


errors(bytes, Idx())
errors(bytes, I(10 ** 30))


class ASetSubclassWhoseNameIsLongerThanFiftyBytesInTotalLength(set):
    pass


print(len(ASetSubclassWhoseNameIsLongerThanFiftyBytesInTotalLength([1, 2])))


class M:
    def keys(self):
        return ("a",)

    def __getitem__(self, k):
        return 1

    p = property(dict)


print(M().p)
print(callable(exit))


class Meta(type):
    pass


class C(metaclass=Meta):
    pass


class E(C):
    pass


print(issubclass(E, C), issubclass(C, E))
