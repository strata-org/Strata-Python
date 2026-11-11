# == of two nested typing aliases costs CPython four C levels per level: inside a deep comparison
# of nested tuples, it passes CPython's C recursion limit.
from typing import TypeGuard


def mk(d):
    x = int
    for _ in range(d):
        x = TypeGuard._getitem(TypeGuard, x)
    return x


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
