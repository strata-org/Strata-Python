# Test: Slots: layouts across subclasses and a diamond, mangled names, and an unset slot.
class A:
    __slots__ = ("y", "x", "__p")
    z = 1
    def setp(self, v):
        self.__p = v
        return self.__p
a = A()
a.x = 3
a.y = 4
print(a.x, a.y, a.z, a.setp(7))
del a.x
class B(A):
    __slots__ = "w"
b = B()
b.w = 1
b.x = 2
class C(A):
    pass
c = C()
c.q = 5
c.y = 6
print(c.q, c.y)
class J:
    __slots__ = ("__dict__", "k")
j = J()
j.k = 1
j.m = 2
print(j.k, j.m)
class M:
    pass
class N(M, B):
    __slots__ = ("n",)
n = N()
n.n = 1
n.w = 2
n.x = 3
n.y = 4
print(n.n, n.w, n.x, n.y, b.w, b.x)
class Q:
    __slots__ = ("v",)
    def __eq__(self, other):
        return True
print(Q() == Q(), Q() != 1)
a2 = A()
a2.x
