# A metaclass with its own __getattr__ runs type.__getattribute__ through its wrapper, which costs
# CPython a C level: 800 nested property reads on classes, then a lookup whose key is a tuple
# nested 800 deep, run past CPython 3.12's C recursion limit, which raises RecursionError. The model
# counts the level, so it stops with a gap.
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
class M(type):
    def __getattr__(cls, name):
        return 0
    @property
    def p(cls):
        if cls.n == 0:
            return len(repr(t))
        return cs[cls.n - 1].p
cs = {}
for i in range(800 + 1):
    cs[i] = M("C", (), {"n": i, "__module__": "m"})
print(cs[800].p)

