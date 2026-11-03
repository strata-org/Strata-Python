# reversed: __reversed__ first, else __len__ and __getitem__; the reverse iterators end for good.
def count(it):
    n = 0
    for _ in it:
        n += 1
    return n


class Seq:
    def __len__(self):
        print("len")
        return 3

    def __getitem__(self, i):
        print("getitem", i)
        return i * 10


class Own:
    def __reversed__(self):
        return iter("own")


class NotRev:
    __reversed__ = None

    def __len__(self):
        return 1

    def __getitem__(self, i):
        return i


r = reversed(Seq())
print(type(r).__name__, r.__length_hint__())
for x in r:
    print(x)
print(r.__length_hint__())
print(next(reversed(Own())))
for x in reversed([1, 2, 3]):
    print(x)
for x in reversed((4, 5)):
    print(x)
for x in reversed("ab"):
    print(x)
print(type(reversed([])).__name__, type(reversed(())).__name__)
l = [1, 2, 3]
r = reversed(l)
print(next(r), r.__length_hint__())
del l[:]
print(count(r), r.__length_hint__())
l[0:0] = [7, 8, 9]
print(count(r))
d = {"x": 1, "y": 2, "z": 3}
for k in reversed(d):
    print(k)
it = reversed(d)
print(it.__length_hint__(), type(it).__name__)
d2 = {1: 0}
it = reversed(d2)
d2[2] = 0
try:
    next(it)
except RuntimeError as e:
    print(e.args[0])
del d2[2]
try:
    next(it)
except RuntimeError as e:
    print(e.args[0])
print(it.__length_hint__())
for args, kwargs in [((), {}), ((1, 2), {}), (([],), {"x": 1}), ((5,), {}), ((NotRev(),), {})]:
    try:
        reversed(*args, **kwargs)
    except TypeError as e:
        print(e.args[0])


class Short:
    def __init__(self):
        self.n = 3

    def __len__(self):
        return self.n

    def __getitem__(self, i):
        if i == 1:
            raise IndexError
        return i


r = reversed(Short())
print(next(r))
print(count(r), r.__length_hint__())
s = Short()
r = reversed(s)
s.n = 1
print(r.__length_hint__())


class Stop:
    def __len__(self):
        return 2

    def __getitem__(self, i):
        raise StopIteration


print(count(reversed(Stop())))


class Bad:
    def __len__(self):
        return 3

    def __getitem__(self, i):
        if i == 2:
            raise ValueError("x")
        return i


r = reversed(Bad())
try:
    next(r)
except ValueError as e:
    print("ValueError", e.args[0])
print(r.__length_hint__(), count(r))


class P:
    @property
    def __reversed__(self):
        return None

    def __len__(self):
        return 1

    def __getitem__(self, i):
        return i


try:
    reversed(P())
except TypeError as e:
    print(e.args[0])
class M:
    __getitem__ = dict.__getitem__

    def __len__(self):
        return 1


print(type(reversed(M())).__name__)


# The views come with the dict methods.
for v in reversed(d.values()):
    print(v)
for k, v in reversed(d.items()):
    print(k, v)
