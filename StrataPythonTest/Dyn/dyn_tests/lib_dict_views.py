# The dict views through their own dunders: live length and iteration, membership, reversed,
# repr, the comparisons with sets and views, the set operations in both orders, isdisjoint, and
# the items view's symmetric difference while a value's __eq__ grows the other dict.
def L(view):
    out = []
    for x in view:
        out.append(x)
    return out


d = {1: "a", 2: "b"}
k = d.keys()
v = d.values()
it = d.items()
print(type(k).__name__, k.__len__(), L(k), L(v), L(it))
d[3] = "c"
print(k.__len__(), L(k), L(reversed(k)), L(reversed(v)), L(reversed(it)))
print(repr(k), repr(v), repr(it))
print(k.__contains__(1), k.__contains__(9), it.__contains__((1, "a")), it.__contains__((1, "z")),
      it.__contains__([1, "a"]), it.__contains__((1,)))
print(k.__eq__(set([1, 2, 3])), k.__eq__(set([1, 2])), k.__ne__(set([1])), k.__lt__(set([1, 2, 3, 4])),
      k.__le__(set([1, 2, 3])), k.__gt__(set([1])), k.__ge__(set([1, 2, 3])), k.__eq__([1, 2, 3]))
print(it.__eq__(set([(1, "a"), (2, "b"), (3, "c")])), k.__eq__({1: 0, 2: 0, 3: 0}.keys()))
print(sorted(k.__and__(set([1, 5]))), sorted(k.__or__([7])), sorted(k.__sub__(set([1]))),
      sorted(k.__xor__(set([1, 9]))), sorted(k.__rand__([2, 8])), sorted(k.__ror__([7])),
      sorted(k.__rsub__([1, 8])), sorted(k.__rxor__([3, 4])))
print(type(k.__and__(set([1]))).__name__, k.isdisjoint([8]), k.isdisjoint(set([1])), it.isdisjoint([(1, "a")]))
n = {1: 10, 2: 20, 3: 30}.items()
print(sorted(n.__and__(set([(1, 10), (5, 50)]))), sorted(n.__sub__([(2, 20)])), sorted(n.__or__([(4, 40)])))


class A:
    def __init__(self, v):
        self.v = v

    def __eq__(self, other):
        d2[5] = 0
        return self.v == other.v

    def __hash__(self):
        return 0


d1 = {1: A(1)}
d2 = {1: A(2)}
pairs = d1.items().__xor__(d2.items())
keys = []
for p in pairs:
    keys.append(p[0])
print(len(pairs), sorted(keys))
e = {}
print(repr(e.keys()), L(e.items()), e.keys().__len__())
r = {}
r[1] = r.items()
print(repr(r[1]))
