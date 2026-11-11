# A typing subscription whose key's hash equals a stored key's: CPython compares the two keys, and
# inside a deep comparison of nested tuples that passes its C recursion limit.
from typing import List, TypeGuard


def mk(d, leaf):
    x = leaf
    for _ in range(d):
        x = TypeGuard._getitem(TypeGuard, x)
    return x


stored = List[mk(800, -1)]


def nest(n, leaf):
    t = leaf
    for _ in range(n):
        t = (t,)
    return t


class E:
    def __eq__(self, o):
        print("inner", List[mk(800, -2)] is stored)
        return True
    __hash__ = object.__hash__


print("small", nest(10, E()) == nest(10, E()))
try:
    print("deep", nest(7100, E()) == nest(7100, E()))
except RecursionError:
    print("RecursionError")
