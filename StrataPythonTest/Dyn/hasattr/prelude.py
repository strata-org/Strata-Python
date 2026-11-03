class C:
    __slots__ = ('a', '__dict__')
    x = 1
    def m(self): return 1
    @property
    def p(self): return 2
    @classmethod
    def cm(cls): return 3
    @staticmethod
    def sm(): return 4
c = C()
c.a = 5
def f(): pass
class D(C): pass
d = D()
class E:
    pass
e = E()
class M(type):
    pass
class K(metaclass=M):
    pass
pr = property(f)
st = staticmethod(f)
cl = classmethod(f)
sp = super(D, d)
