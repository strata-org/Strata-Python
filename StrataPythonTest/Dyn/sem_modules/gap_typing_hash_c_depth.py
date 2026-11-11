# The hash of a nested typing alias costs CPython three C levels per level: inside a deep
# comparison of nested tuples, it passes CPython's C recursion limit.
from typing import List
def mk(d):
    x = int
    for _ in range(d):
        x = List[x]
    return x
A = mk(800)
def nest(n, leaf):
    t = leaf
    for _ in range(n):
        t = (t,)
    return t
class E:
    def __eq__(self, o):
        print("inner", {A: 1}[A])
        return True
    __hash__ = object.__hash__
print("small", nest(10, E()) == nest(10, E()))
try:
    print("deep", nest(7900, E()) == nest(7900, E()))
except RecursionError:
    print("RecursionError")
