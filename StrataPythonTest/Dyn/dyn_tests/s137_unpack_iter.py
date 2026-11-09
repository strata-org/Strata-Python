# Test: a, b = x, f(*x) and **m over user iterators, __getitem__ objects and built-in iterators, and the dispatch of class calls
class It:
    def __init__(self, n):
        self.i = 0
        self.n = n
    def __iter__(self):
        return self
    def __next__(self):
        if self.i >= self.n:
            raise StopIteration
        self.i += 1
        return self.i
a, b = It(2)
print(a, b)
a, b = iter([1, 2])
print(a, b)
class G:
    def __getitem__(self, i):
        if i >= 2:
            raise IndexError
        return i
a, b = G()
print(a, b)
class Bad:
    def keys(self):
        raise AttributeError("x")
try:
    print(**Bad())
except TypeError as e:
    print(e.args[0], e.__context__ is None, e.__suppress_context__)
try:
    {**Bad()}
except TypeError as e:
    print(e.args[0], e.__context__ is None)
class K:
    def keys(self):
        return 5
try:
    {**K()}
except TypeError as e:
    print(e.args[0], e.__context__ is None)
class NI:
    def __iter__(self):
        raise TypeError("inner")
try:
    1 in NI()
except TypeError as e:
    print(e.args[0], e.__context__ is None)
class G:
    def __getitem__(self, k):
        raise KeyError("zz")
    def keys(self):
        return ["a"]
try:
    print(**G())
except TypeError as e:
    print(e.args[0], e.__context__ is None)
try:
    {**G()}
except KeyError as e:
    print("KeyError", e.args[0])
class KI:
    def __init__(self):
        self.i = 0
    def __iter__(self):
        return self
    def __next__(self):
        self.i += 1
        if self.i > 3:
            raise StopIteration
        return ["sep", "end", "sep"][self.i - 1]
class M:
    def keys(self):
        return KI()
    def __getitem__(self, k):
        print("get", k)
        return ""
try:
    print(**M())
except TypeError as e:
    print(e.args[0])
d = {**M()}
print(len(d))
try:
    print(end="", **M())
except TypeError as e:
    print(e.args[0])
class H:
    def __init__(self, n):
        self.n = n
    def __hash__(self):
        print("hash", self.n)
        return self.n
    def __eq__(self, o):
        print("eq", self.n)
        return self is o
class M:
    def __init__(self, ks):
        self.ks = ks
    def keys(self):
        return self.ks
    def __getitem__(self, k):
        print("get", k.n)
        return 0
d = {**M([H(1), H(2)])}
print(len(d))
try:
    print(**M([H(3)]))
except TypeError as e:
    print(e.args[0])
class Meta(type):
    def __call__(cls, *a):
        print("meta call", len(a))
        return super().__call__(*a)
class A(metaclass=Meta):
    def __init__(self, x):
        print("init", x)
a = A(1)
print(type(a).__name__)
class B:
    def __new__(cls, x):
        print("new", x)
        return 5
    def __init__(self, x):
        print("never")
print(B(2))
class C:
    def __init__(self):
        return 3
try:
    C()
except TypeError as e:
    print(e.args[0])
class D:
    def __call__(self, y):
        return y + 1
print(D()(4))
class E:
    __call__ = None
try:
    E()(1)
except TypeError as e:
    print(e.args[0])
print(type(3).__name__)
T = type("T", (), {"__module__": "m"})
print(T.__name__)
class F:
    @staticmethod
    def s(x):
        return x * 2
    @classmethod
    def c(cls, x):
        return cls.__name__
print(F.s(3), F.c(1), F().s(2))
class Meta2(type):
    pass
class G(metaclass=Meta2):
    def __init__(self, q):
        self.q = q
print(G(9).q)
class H(D):
    pass
print(H()(10))
class I:
    def __new__(cls):
        return object.__new__(D)
    def __init__(self):
        print("I init never")
print(type(I()).__name__)
class J(Exception):
    def __init__(self, a):
        print("J init", a)
j = J(5)
print(j.args[0])
try:
    object(1)
except TypeError as e:
    print(e.args[0])
class K:
    pass
try:
    K(1)
except TypeError as e:
    print(e.args[0])
