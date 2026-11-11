# list, tuple, set, frozenset and dict as constructors: their protocol calls, errors and subclasses.
class X:
    def __init__(self, n):
        self.n = n

    def __len__(self):
        print("len")
        return self.n

    def __length_hint__(self):
        print("hint")
        return self.n

    def __iter__(self):
        print("iter")
        return iter(range(self.n))


class H:
    def __length_hint__(self):
        print("hint")
        return 2

    def __iter__(self):
        print("iter")
        return iter([1, 2])


class Down:
    def __init__(self, n):
        self.n = n

    def __iter__(self):
        return self

    def __next__(self):
        if self.n == 0:
            raise StopIteration
        self.n -= 1
        return self.n


class Mp:
    def keys(self):
        print("keys")
        return ["a", "b"]

    def __getitem__(self, k):
        print("get", k)
        return k * 2


class L(list):
    pass


class T(tuple):
    pass


class FS(frozenset):
    pass


class D(dict):
    pass


def errors(f, *args, **kwargs):
    try:
        f(*args, **kwargs)
    except (TypeError, ValueError) as e:
        print(type(e).__name__, e.args[0])


for f in (list, tuple, set, frozenset):
    print("--", f.__name__)
    print(len(f(X(2))), len(f(H())), len(f(Down(4))), len(f()), len(f("abc")), len(f(range(3))))
    for args, kwargs in [((1, 2), {}), ((), {"x": 1}), ((5,), {})]:
        errors(f, *args, **kwargs)
l = list(Down(3))
print(l[0], l[1], l[2], len(l))
t = tuple(Down(3))
print(t[0], t[2], len(t), tuple(t) == t)
s = set(Down(5))
print(len(s), 4 in s, 0 in s)
fs = frozenset(Down(3))
print(len(fs), 2 in fs, hash(fs) == hash(frozenset([0, 1, 2])), frozenset(fs) is fs)
l = [1, 2]
l.__init__([3])
print(len(l), l[0])
s = {1, 2}
s.__init__([5])
print(len(s), 5 in s)
d = dict(Mp())
print(d["a"], d["b"], len(d))
d = dict([("a", 1), "bc", [3, 4]], z=9)
print(d["a"], d["b"], d[3], d["z"], len(d))
d = dict(Down(0), q=1)
print(len(d), d["q"])
print(len(dict({1: 2, 3: 4})), len(dict()), dict(a=1)["a"])
errors(dict, 1, 2)
errors(dict, [1])
errors(dict, ["abc"])
errors(dict, 5)
print(len(L([1, 2])), type(L(Down(2))).__name__, len(T([1, 2])), type(T(())).__name__)
print(len(FS([1])), type(FS(Down(2))).__name__, type(D(a=1)).__name__, D(a=1)["a"], len(D({1: 2})))
errors(FS, 1, 2)


class Pair:
    def __init__(self, k, v):
        self.items = [k, v]

    def __iter__(self):
        return iter(self.items)


class SlowPair:
    def __init__(self, k, v):
        self.k, self.v, self.i = k, v, 0

    def __iter__(self):
        return self

    def __next__(self):
        self.i += 1
        if self.i == 1:
            return self.k
        if self.i == 2:
            return self.v
        raise StopIteration


d = dict([Pair("p", 1), SlowPair("s", 2), ("t", 3)])
print(d["p"], d["s"], d["t"], len(d))
errors(dict, [SlowPair("a", 1), Pair(1, 2), 7])
errors(dict, [Down(3)])


class LoggedT(tuple):
    def __init__(self, it):
        print("init", len(self))


class LoudDown(Down):
    def __next__(self):
        v = super().__next__()
        print("next", v)
        return v


t = LoggedT(LoudDown(3))
print(len(t), type(t).__name__)


class NegLen:
    def __len__(self):
        return -1

    def __iter__(self):
        return iter([])


class BadHint:
    def __length_hint__(self):
        return "x"

    def __iter__(self):
        return iter([])


errors(list, NegLen())
errors(tuple, BadHint())
print(len(set(NegLen())), len(frozenset(BadHint())))
