# Test: an old part inside the dict of a dict view, and inside a slice's bound, is read at entry:
# OLD(len(xs)) in tables[len(OLD(xs))].values(), and OLD(a) in xs[OLD(a):], not the slice.
from pyhard import loop_invariant, OLD

def f(tables, xs, a, n):
    i = 0
    loop_invariant(lambda: all(v > 0 for v in tables[len(OLD(xs))].values()))
    loop_invariant(lambda: len(xs[OLD(a):]) >= 0)
    loop_invariant(lambda: len(xs[OLD(a):OLD(n)]) >= 0)
    while i < n:
        i += 1
    return i

print(f({2: {"k": 1}}, [1, 2], 0, 2))
