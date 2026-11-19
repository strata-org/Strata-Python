# Test: invariants that are false at some entries of their loop's head, one per lowering path:
# a false comparison, an exception inside P (an unbound local, a TypeError, a ZeroDivisionError),
# and, or, not and a conditional expression giving False, and a falsy result that isn't a bool.
from pyhard import loop_invariant

def f(n):
    i = 0
    s = "a"
    loop_invariant(lambda: i < 2)
    loop_invariant(lambda: later > 0)
    loop_invariant(lambda: s < i or i == 0)
    loop_invariant(lambda: 1 // (2 - i) >= 0)
    loop_invariant(lambda: i > 0 and i < 3)
    loop_invariant(lambda: not i)
    loop_invariant(lambda: (i if i < 2 else 0) > 0)
    loop_invariant(lambda: i - 1)
    while i < n:
        i += 1
    later = 1
    return i + later

print(f(3))
