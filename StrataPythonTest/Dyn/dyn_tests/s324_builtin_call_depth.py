# A call of a built-in such as repr costs CPython a C level, and a dict key's comparison costs
# levels too: 800 nested calls of repr, then a lookup whose key is a tuple nested 800 deep, run past
# CPython 3.12's C recursion limit, which raises RecursionError. The model counts the calls, so it
# stops with a gap; if it didn't, the run would end with a result.
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
for _ in range(6500):
    t = (t,)
class R:
    def __init__(self, n):
        self.n = n
    def __repr__(self):
        if self.n == 0:
            return repr(t)
        return repr(R(self.n - 1))
print(len(repr(R(800))))
