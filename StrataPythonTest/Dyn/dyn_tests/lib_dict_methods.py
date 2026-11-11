# The methods of dict: one hash per lookup, the empty-dict shortcut of pop, update's merge and
# count error, fromkeys on dict, set and iterator sources and on a subclass, and the argument
# errors.
class K:
    def __init__(self, v):
        self.v = v

    def __hash__(self):
        print("hash", self.v)
        return hash(self.v)

    def __eq__(self, o):
        print("eq", self.v)
        return isinstance(o, K) and o.v == self.v

    def __repr__(self):
        return f"K({self.v})"


def show(f, *a, **k):
    try:
        print(repr(f(*a, **k)))
    except (TypeError, KeyError, ValueError) as e:
        print(type(e).__name__, e.args)


d = {K(1): "a"}
show(d.get, K(1))
show(d.get, K(2), 0)
show(d.setdefault, K(3))
show(d.setdefault, K(1), "z")
show(d.pop, K(9))
show(d.pop, K(9), "dflt")
show({}.pop, K(5))
show({}.pop, K(5), 1)
show({}.popitem)
show({1: 2, 3: 4}.popitem)
show(d.get)
show(d.get, 1, 2, 3)
show(d.pop)
show(d.setdefault)
show(d.get, [1])
show(d.pop, [1])
show({}.pop, [1])
u = {"k": 0}
show(u.update, 1, 2)
show(u.update, [(1, 2)], x=3)
print(u)
show(u.update, {7: 8})
show(u.update, x=4)
print(u)
show(dict.fromkeys, [1, 2])
show(dict.fromkeys, "ab", 0)
show(dict.fromkeys, {3: 4, 5: 6})
show(dict.fromkeys)
show(dict.fromkeys, 1)


class D(dict):
    def __setitem__(self, k, v):
        print("setitem", k)
        super().__setitem__(k, v)


show(D.fromkeys, [1, 2])
print(type(D.fromkeys([1])).__name__)
show(D.fromkeys, {1: 2})
dd = {1: 2}
c = dd.copy()
print(c, c is dd, type(D(a=1).copy()).__name__)
show(dd.copy, 1)
show(dd.clear, 1)
dd.clear()
print(dd)


class It:
    def __init__(self):
        self.n = 3

    def __iter__(self):
        return self

    def __next__(self):
        if self.n == 0:
            raise StopIteration
        self.n -= 1
        return self.n


print(dict.fromkeys(It(), "v"))
e = {}
e.update([(1, "a"), (2, "b")])
print(e)
print(dict.fromkeys(set([3, 1, 2]), 0), dict.fromkeys(frozenset([5, 4])))


class SortedDict(dict):
    def sorted_keys(self):
        out = []
        for k in dict.__iter__(self):
            out.append(k)
        out.sort()
        return out

    def __iter__(self):
        return iter(self.sorted_keys())

    def keys(self):
        print("keys")
        return self.sorted_keys()

    def __getitem__(self, k):
        print("getitem", k)
        return super().__getitem__(k)


sd = SortedDict({2: "b", 1: "a"})
print(sd.copy(), SortedDict().copy())
