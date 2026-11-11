# The methods of set and frozenset: their arguments in order, sets merged, dicts by their keys,
# other iterables walked item by item with CPython's early stops, results of the base type, and
# the argument errors.
class It:
    def __init__(self, xs):
        self.xs = list(xs)

    def __iter__(self):
        print("iter")
        return self

    def __next__(self):
        if not self.xs:
            raise StopIteration
        x = self.xs.pop(0)
        print("next", x)
        return x


class H:
    def __init__(self, v):
        self.v = v

    def __hash__(self):
        print("hash", self.v)
        return self.v

    def __eq__(self, o):
        return isinstance(o, H) and o.v == self.v


def show(f, *a, **k):
    try:
        r = f(*a, **k)
        print(type(r).__name__, sorted(r) if isinstance(r, (set, frozenset)) else r)
    except (TypeError, KeyError, ValueError) as e:
        print(type(e).__name__, e.args)


s = {1, 2, 3}
show(s.union, [4], (5,), {6: 0})
show(s.intersection, It([2, 9, 3, 1, 7]))
it = iter([2, 1, 3])
print({1}.issubset(it), list(it))
it = iter([1, 2, 3])
print(sorted({1}.intersection(it)), list(it))
show(s.difference, It([1]), [2])
show(s.difference, {1: 0})
show(s.symmetric_difference, It([3, 4]))
show(s.issuperset, It([1, 5, 2]))
show(s.isdisjoint, It([7, 2, 8]))
show(s.issubset, [1, 2, 3, 4])
show(s.issubset, {1, 2})
show(s.issuperset, {1})
show(s.isdisjoint, {9})
show(frozenset([1, 2]).union, [3])
show(frozenset([1, 2]).intersection)
show(frozenset([1, 2]).difference)
fs = frozenset([1])
print(fs.copy() is fs, type(set([1]).copy()).__name__)


class S(set):
    pass


class F(frozenset):
    pass


show(S([1]).union, [2])
show(F([1]).union, [2])
print(type(F([1]).copy()).__name__)
u = {1, 2}
u.update(It([3]), {4}, {5: 0}, [6])
print(sorted(u))
u.intersection_update([1, 2, 3], It([2, 3]))
print(sorted(u))
u = {1, 2, 3, 4}
u.difference_update([1], It([2]))
print(sorted(u))
u.symmetric_difference_update(It([3, 9]))
print(sorted(u))
u.symmetric_difference_update({4: 0, 7: 0})
print(sorted(u))
u.add(H(5))
print(len(u))
u.discard(H(5))
u.discard(99)
show(u.remove, 99)
show(u.remove, [1])
u.discard({1})
show(u.remove, {1})
v = {frozenset([1])}
v.remove({1})
print(v)
show(set().pop)
p = {7}
print(p.pop(), p)
u.clear()
print(u)
show(s.union, 1)
show(s.update, 1)
show(s.add)
show(s.add, 1, 2)
show(s.issubset)
show(s.copy, 1)
print(sorted(s.union()), sorted(s.intersection(s)), s.difference(s) == set(), len(s.symmetric_difference(s)), s.isdisjoint(s))
for f in [set([frozenset([1]), 2]).difference, set([frozenset([1]), 2]).difference_update]:
    show(f, [set([1])])


class HS(set):
    def __hash__(self):
        return 0


class B:
    def __hash__(self):
        return 0

    def __eq__(self, other):
        raise TypeError("boom")


w = set([B(), frozenset([1])])
w.remove(HS([1]))
print(len(w))


class LenSet(set):
    def __len__(self):
        print("len called")
        return 5


print({1: 2}.keys().__eq__(LenSet([1])), {1: 2}.keys().isdisjoint(LenSet([7])))
big = set(range(20))
show(big.difference, {1: 0, 2: 0})
