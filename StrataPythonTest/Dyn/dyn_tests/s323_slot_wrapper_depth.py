# A call of a slot wrapper (object.__setattr__) or a method-wrapper (q.__setattr__) costs CPython a
# C level. With 30 such calls nested, the repr of a tuple nested 8920 deep still fits CPython 3.12's
# C recursion limit, but not the model's, which stops 995 levels earlier: the run stops with a gap.
# If the model didn't count those levels, the repr would fit and the run would agree with CPython.
def nest(d):
    t = ()
    for _ in range(d):
        t = (t,)
    return t
class P:
    def __init__(self, n):
        object.__setattr__(self, "n", n)
    @property
    def x(self):
        return None
    @x.setter
    def x(self, v):
        if self.n == 0:
            print(len(repr(nest(8920))))
            return
        q = P(self.n - 1)
        if self.n % 2 == 0:
            object.__setattr__(q, "x", v)
        else:
            q.__setattr__("x", v)
p = P(30)
p.x = 1
