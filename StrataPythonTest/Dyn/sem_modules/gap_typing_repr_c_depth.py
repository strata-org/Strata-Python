# The repr of a nested typing alias costs CPython four C levels per level: inside a deep
# comparison of nested tuples, it passes CPython's C recursion limit.
from typing import TypeGuard
def mk(d):
    x = int
    for _ in range(d):
        x = TypeGuard._getitem(TypeGuard, x)
    return x
A = mk(440)
def nest(n, leaf):
    t = leaf
    for _ in range(n):
        t = (t,)
    return t
class E:
    def __eq__(self, o):
        print("inner", len(repr(A)))
        return True
    __hash__ = object.__hash__
print("small", nest(10, E()) == nest(10, E()))
try:
    print("deep", nest(8400, E()) == nest(8400, E()))
except RecursionError:
    print("RecursionError")
