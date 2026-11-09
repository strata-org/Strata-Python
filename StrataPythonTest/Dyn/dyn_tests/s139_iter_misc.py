# Test: in over user iterables, the live set walk, mutation during for loops, the call orders of *x, and a method recursion that stays within the depth
# Z keeps the set displays below from being all constants, so that their order stays CPython's.
Z = 0
class C:
    __contains__ = None
    def __iter__(self):
        return iter([1])
try:
    1 in C()
except TypeError as e:
    print(e.args[0])
class D:
    def __contains__(self, x):
        print("contains", x)
        return []
print(1 in D(), 1 not in D())
class E:
    def __iter__(self):
        return iter([1, 2])
    def __getitem__(self, i):
        print("never")
print(2 in E(), 3 not in E())
class Eq:
    def __eq__(self, o):
        print("Eq.eq", o)
        return True
class F:
    def __iter__(self):
        return iter([5, 6])
print(Eq() in F())
class G:
    def __getitem__(self, i):
        if i > 3:
            raise IndexError
        print("get", i)
        return i
print(2 in G(), 9 in G())
class H:
    pass
try:
    1 in H()
except TypeError as e:
    print(e.args[0])
class NE:
    def __iter__(self):
        raise ValueError("ve")
try:
    1 in NE()
except ValueError as e:
    print("VE", e.args[0])
class BadIt:
    def __iter__(self):
        return 3
try:
    1 in BadIt()
except TypeError as e:
    print(e.args[0])
class Bool:
    def __bool__(self):
        raise ValueError("nb")
class D2:
    def __contains__(self, x):
        return Bool()
try:
    1 in D2()
except ValueError as e:
    print("VE", e.args[0])
x = [1]
class Grow:
    def __init__(self):
        self.l = [0, 0, 0]
    def __iter__(self):
        return iter(self.l)
g = Grow()
class Ap:
    def __eq__(self, o):
        g.l += [0]
        print("eq", len(g.l))
        return len(g.l) > 6
print(Ap() in g)
for x in {(5 + Z), 1, 9, 33}:
    print(x)
s = {(1 + Z), 2, 3}
for x in s:
    if x == 1:
        s -= {(2 + Z)}
        s |= {(17 + Z)}
    print(x)
s = {(1 + Z), 2, 3}
try:
    for x in s:
        s |= {x + 10}
except RuntimeError as e:
    print(e.args[0])
d = {1: 1}
try:
    for k in d:
        d[k + 1] = 0
except RuntimeError as e:
    print(e.args[0], len(d))
l = [1, 2]
for x in l:
    if len(l) < 5:
        l += [x * 10]
    print(x)
d = {1: 2, 3: 4}
for k in iter(d):
    print(k)
s = 0
for k in d:
    s += k
print(s, 3 in iter([3]) if False else 0)
class It:
    def __init__(self, n):
        self.i = 0
        self.n = n
    def __iter__(self):
        print("iter")
        return self
    def __next__(self):
        if self.i >= self.n:
            raise StopIteration
        self.i += 1
        return self.i
    def __len__(self):
        print("len")
        raise ValueError("no len")
try:
    print(*It(2))
except ValueError as e:
    print("VE", e.args[0])
try:
    [*It(2)]
except ValueError as e:
    print("VE", e.args[0])
class It2(It):
    def __len__(self):
        print("len2")
        return 1
print(*It2(3))
print(len([*It2(3)]))
try:
    a, b, *c, d = It2(2)
except ValueError as e:
    print(e.args[0])
try:
    a, b, *c, d = It2(1)
except ValueError as e:
    print(e.args[0])
a, *c, d = It2(5)
print(a, len(c), d)
class G:
    def __getitem__(self, i):
        if i > 2:
            raise IndexError
        return i
print(*G())
a, *b = G()
print(a, len(b))
print({*G()} == {(0 + Z), 1, 2})
def nest_list(n, x):
    a = x
    i = 0
    while i < n:
        a = [a]
        i += 1
    return a
def nest_tuple(n):
    t = ()
    i = 0
    while i < n:
        t = (t,)
        i += 1
    return t
A = nest_list(7000, {nest_tuple(890): 1})
B = nest_list(7000, {nest_tuple(890): 1})
class C:
    def m(self, n):
        if n == 0:
            try:
                return A == B
            except RecursionError:
                return "RecursionError"
        return self.m(n - 1)
print(C().m(850))
del A, B
