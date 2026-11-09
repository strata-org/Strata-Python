# Test: range slicing, range.__reversed__ and range iterators
class I:
    def __index__(self):
        print("index")
        return 3
r = range(I())
print(len(r), r[-1])
r = range(5, I(), -1)
print(len(r), r[0])
print(len(range(10, 0, -3)), range(10, 0, -3)[2])
r = range(0, 10, 2)
print(r[1:3][0], len(r[1:3]), len(r[::-1]), r[::-1][0])
print(range(3) == range(0, 3), range(0) == range(5, 2), range(1, 2, 5) == range(1, 3, 7))
try:
    r[10]
except IndexError as e:
    print(e.args[0])
print(3 in r, 4 in r, -2 in r)
b = range(-2**70, 2**70, 2**69)
print(len(b), type(iter(b)).__name__)
bi = iter(b)
next(bi)
print(next(bi) == -2**70 + 2**69, bi.__length_hint__())
c = range(2**63 - 2, 2**63 + 2)
ci = iter(c)
print(type(ci).__name__, next(ci) - 2**63)
e = range(-5, 2**63 - 1)
print(type(iter(e)).__name__)
f = range(0, 2**63-1, 2**62)
print(type(iter(f)).__name__)
rv = range(5).__reversed__()
print(type(rv).__name__, next(rv))
class S:
    def __eq__(self, o):
        print("S.eq", o)
        return o == 2
c = [0]
def f():
    c[0] += 1
    return c[0]
it = iter(f, S())
print(next(it), next(it, "end"), next(it, "end2"))
class V:
    def __eq__(self, o):
        print("V.eq")
        return False
def g():
    return V()
it2 = iter(g, 5)
print(type(next(it2)).__name__)
def h():
    raise StopIteration
it3 = iter(h, 1)
print(next(it3, "stop"), next(it3, "stop2"))
class SE(StopIteration):
    pass
def h2():
    raise SE
print(next(iter(h2, 1), "sub"))
class B:
    def __eq__(self, o):
        raise ValueError("bad eq")
def k():
    return 1
it4 = iter(k, B())
try:
    next(it4)
except ValueError as e:
    print(e.args[0])
try:
    next(it4)
except ValueError as e:
    print("again", e.args[0])
print(len([*iter(lambda: 0, 0)]))
class It:
    def __init__(self):
        self.i = 0
    def __iter__(self):
        return self
    def __next__(self):
        self.i += 1
        if self.i > 2:
            raise StopIteration
        return self.i
it = It()
print(next(it), next(it), next(it, "d"))
class SI(StopIteration):
    pass
class It2:
    def __next__(self):
        raise SI("x")
    def __iter__(self):
        return self
print(next(It2(), "dflt"))
try:
    next(It2())
except SI as e:
    print("SI", e.args[0])
print(len([*It2()]), len({*It2()}))
def f(*a):
    return len(a)
print(f(*It2()))
a, *b = It2() if False else [1]
print(a, len(b))
print(1 in It2())
class It3:
    def __next__(self):
        raise ValueError("v")
    def __iter__(self):
        return self
for t in [lambda: [*It3()], lambda: 1 in It3(), lambda: f(*It3()), lambda: {*It3()}]:
    try:
        t()
    except ValueError as e:
        print("VE", e.args[0])
# A range too long for a C long iterates backwards with a longrange_iterator.
for r in (range(2 ** 70), range(-2 ** 63, 0), range(0, 10, -2 ** 63), range(5, 2 ** 63 - 1)):
    print(type(r.__reversed__()).__name__)
