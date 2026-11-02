# Test: property subclasses: an __init__ of their own, and a docstring in the instance's __dict__
class P(property):
    def __init__(self, x):
        super().__init__(lambda s: x, doc="d")
class C:
    a = P(5)
print(C().a)
class Q(property):
    pass
q = Q(doc="up")
print(q.__doc__)
class D:
    @property
    def v(self): return 3
    @v.setter
    def v(self, x): print("set", x)
d = D()
d.v = 4
print(d.v)
property(x=1)
