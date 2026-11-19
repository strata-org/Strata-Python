# Test: an invariant whose truth test runs a __bool__ that raises is false at every entry.
from pyhard import loop_invariant

class B:
    def __bool__(self):
        raise ValueError("no")

def f(n):
    b = B()
    i = 0
    loop_invariant(lambda: b)
    while i < n:
        i += 1
    return i

print(f(2))
