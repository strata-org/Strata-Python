# Test: isinstance in invariants, with a subclass and a bool, is evaluated at
# each head entry: the first two invariants are True at every entry, and the third is always False.
from pyhard import loop_invariant

class A:
    pass

class B(A):
    pass

def f(xs):
    i = 0
    loop_invariant(lambda: isinstance(i, int) and not isinstance(i, bool))
    loop_invariant(lambda: isinstance(xs[0], A) or isinstance(xs[0], list) if xs else True)
    loop_invariant(lambda: isinstance(xs, tuple))
    while i < len(xs):
        i += 1
    return i

print(f([B(), A()]))
print(f([]))
