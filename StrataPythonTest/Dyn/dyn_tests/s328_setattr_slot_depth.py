# A write on a class with its own __delattr__ runs object.__setattr__ through its wrapper, which
# costs CPython a C level: 800 nested property writes, then a lookup whose key is a tuple nested 800
# deep, run past CPython 3.12's C recursion limit, which raises RecursionError. The model counts
# the level, so it stops with a gap.
def nest(d):
    t = ()
    for _ in range(d):
        t = (t,)
    return t
k1 = nest(800)
k2 = nest(800)
table = {k1: 1}
class Leaf:
    def __repr__(self):
        if table[k2] == 1:
            return "x"
        return "y"
t = Leaf()
for _ in range(7300):
    t = (t,)
class P:
    def __init__(self, n):
        object.__setattr__(self, "n", n)
    def __delattr__(self, name):
        pass
    @property
    def x(self):
        return None
    @x.setter
    def x(self, v):
        if self.n == 0:
            print(len(repr(t)))
            return
        q = P(self.n - 1)
        q.x = v
p = P(800)
p.x = 1

