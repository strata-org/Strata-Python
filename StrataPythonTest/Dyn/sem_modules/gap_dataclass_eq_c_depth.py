# == of two nested dataclass instances costs CPython four C levels per level: inside a deep
# comparison of nested tuples, it passes CPython's C recursion limit.
from dataclasses import dataclass
@dataclass(frozen=True)
class D:
    x: object
def mk(d):
    v = 0
    for _ in range(d):
        v = D(v)
    return v
A = mk(800)
B = mk(800)
def nest(n, leaf):
    t = leaf
    for _ in range(n):
        t = (t,)
    return t
class E:
    def __eq__(self, o):
        print("inner", A == B)
        return True
    __hash__ = object.__hash__
print("small", nest(10, E()) == nest(10, E()))
try:
    print("deep", nest(7100, E()) == nest(7100, E()))
except RecursionError:
    print("RecursionError")
