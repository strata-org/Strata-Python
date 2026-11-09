# Test: the iterator protocol: __iter__ = None, non-iterator results, length hints, iterator entries, the live set walk, and in over an iterator
# Z keeps the set displays below from being all constants, so that their order stays CPython's.
Z = 0
it = iter([1, 2, 3])
print(2 in it)
print(next(it))
class C:
    __iter__ = None
    def __getitem__(self, i):
        return i
try:
    iter(C())
except TypeError as e:
    print(e.args[0])
try:
    for x in C():
        pass
except TypeError as e:
    print(e.args[0])
try:
    [*C()]
except TypeError as e:
    print(e.args[0])
try:
    print(1 in C())
except TypeError as e:
    print(e.args[0])
class C:
    __getitem__ = None
try:
    it = iter(C())
    print(type(it).__name__)
    next(it)
except TypeError as e:
    print(e.args[0])
try:
    [*C()]
except TypeError as e:
    print(e.args[0])
class R:
    def __iter__(self):
        return 5
try:
    iter(R())
except TypeError as e:
    print(e.args[0])
try:
    [*R()]
except TypeError as e:
    print(e.args[0])
try:
    a, *b = R()
except TypeError as e:
    print(e.args[0])
def f(*a): pass
try:
    f(*R())
except TypeError as e:
    print(e.args[0])
try:
    1 in R()
except TypeError as e:
    print(e.args[0])
class N:
    def __next__(self):
        return 1
class R:
    def __iter__(self):
        return N()
it = iter(R())
print(type(it).__name__, next(it))
class R2:
    def __iter__(self):
        return [1]
try:
    iter(R2())
except TypeError as e:
    print(e.args[0])
d = {1: 1, 2: 2}
it = iter(d)
print(next(it))
d[1] = 5
print(next(it))
print(next(it, "end"))
d[9] = 9
print(next(it, "end2"))
s = {(1 + Z), 2, 3}
it = iter(s)
print(next(it))
s -= {(3 + Z)}
s |= {(4 + Z)}
for x in it:
    print(x)
s2 = {(1 + Z), 2, 3}
it2 = iter(s2)
print(next(it2))
s2 -= {(1 + Z)}
s2 |= {(9 + Z)}
for x in it2:
    print(x)
s = {(1 + Z), 2, 3}
it = iter(s)
print(it.__length_hint__())
next(it)
print(it.__length_hint__())
s |= {(7 + Z)}
print(it.__length_hint__())
try:
    next(it)
except RuntimeError as e:
    print(e.args[0], it.__length_hint__())
s -= {(7 + Z)}
print(it.__length_hint__())
try:
    next(it)
except RuntimeError as e:
    print(e.args[0], it.__length_hint__())
l = [1, 2, 3]
it = iter(l)
print(it.__length_hint__())
next(it)
del l[:]
print(it.__length_hint__())
print(next(it, "e"))
l += [5]
print(it.__length_hint__(), next(it, "e2"))
r = iter(range(5))
next(r)
print(r.__length_hint__())
class Lh:
    def __len__(self):
        raise TypeError("no")
    def __length_hint__(self):
        print("hint")
        return 1
    def __iter__(self):
        return iter([1, 2])
print(len([*Lh()]))
class Lh2:
    def __len__(self):
        raise ValueError("v")
    def __iter__(self):
        return iter([1, 2])
try:
    [*Lh2()]
except ValueError as e:
    print("ValueError", e.args[0])
class Lh3:
    __length_hint__ = None
    def __iter__(self):
        return iter([1, 2])
print(len([*Lh3()]))
class Lh4:
    def __length_hint__(self):
        return True
    def __iter__(self):
        return iter([1, 2])
print(len([*Lh4()]))
class Lh5:
    def __length_hint__(self):
        raise TypeError
    def __iter__(self):
        return iter([1, 2])
print(len([*Lh5()]))
class Lh6:
    def __length_hint__(self):
        raise RuntimeError("r")
    def __iter__(self):
        return iter([1, 2])
try:
    [*Lh6()]
except RuntimeError as e:
    print("RuntimeError", e.args[0])
