from pyhard import loop_invariant, OLD

class L(list):
    def __iter__(self):
        return iter([])

class D(dict):
    def items(self):
        return []

def f(t, r, g, ls, d, fs, z, n):
    i = 0
    loop_invariant(lambda: all(c != "z" for c in t))
    loop_invariant(lambda: all(k >= 0 for k in r))
    loop_invariant(lambda: all(x >= 0 for x in g))
    loop_invariant(lambda: all(x > 0 for x in ls))
    loop_invariant(lambda: all(v > 0 for k, v in d.items()))
    loop_invariant(lambda: all(x > 0 for x in fs))
    loop_invariant(lambda: all(1 // x > -1 for x in z))
    loop_invariant(lambda: any(1 // x > 0 for x in z))
    while i < n:
        i += 1
    return i

print(f("ab", range(3), iter([0, 1]), L([-1]), D(a=-1), frozenset([1]), [1, 0], 2))
