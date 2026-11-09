# Test: iter with a __getitem__ object and with a sentinel, next with a default, len, range, and a set iterator's size error
# Z keeps the set displays below from being all constants, so that their order stays CPython's.
Z = 0
class G:
    def __getitem__(self, i):
        if i >= 3:
            raise IndexError
        return i * 10
class L:
    def __len__(self):
        return 4
it = iter(G())
print(next(it), next(it), next(it), next(it, "end"), type(it).__name__)
print(len([1, 2]), len("abc"), len(range(5)), len({1: 2}), len(L()), len(range(0, 10, 3)))
r = range(2, 11, 3)
print(r[0], r[-1], len(r), 5 in r, 6 in r)
c = iter(lambda: next(it2), 2)
it2 = iter([0, 1, 2, 3])
print(next(c), next(c), next(c, "stop"))
x = iter([1])
print(next(x), next(x, None), next(x, None))
s = {(1 + Z), 2}
si = iter(s)
next(si)
s |= {(5 + Z)}
try:
    next(si)
except RuntimeError as e:
    print(e.args[0])
try:
    next(si)
except RuntimeError as e:
    print("again", e.args[0])
for bad in [lambda: len(5), lambda: iter(5), lambda: next([]), lambda: range(1.5), lambda: range(1, 2, 0), lambda: iter(1, 2), lambda: range()]:
    try:
        bad()
    except (TypeError, ValueError) as e:
        print(type(e).__name__, e.args[0])
