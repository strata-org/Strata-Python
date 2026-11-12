# The hash of a nested frozen dataclass instance costs CPython three C levels per level: inside a
# deep comparison of nested tuples, it passes CPython's C recursion limit.
from dataclasses import dataclass
@dataclass(frozen=True)
class D:
    x: object
def mk(d):
    v = 0
    for _ in range(d):
        v = D(v)
    return v
A = mk(850)
B = mk(850)
def nest(n, leaf):
    t = leaf
    for _ in range(n):
        t = (t,)
    return t
class E:
    def __eq__(self, o):
        print("inner", len({A: 1}))
        return True
    __hash__ = object.__hash__
print("small", nest(10, E()) == nest(10, E()))
try:
    print("deep", nest(7500, E()) == nest(7500, E()))
except RecursionError:
    print("RecursionError")
