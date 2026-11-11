# == of two typing unions hashes their arguments, three C levels per level of a nested alias:
# inside a deep comparison of nested tuples, it passes CPython's C recursion limit.
from typing import List, Union
def mk(d):
    x = int
    for _ in range(d):
        x = List[x]
    return x
X = mk(800)
U1 = Union[X, int]
U2 = Union[int, X]
def nest(n, leaf):
    t = leaf
    for _ in range(n):
        t = (t,)
    return t
class E:
    def __eq__(self, o):
        print("inner", U1 == U2)
        return True
    __hash__ = object.__hash__
print("small", nest(10, E()) == nest(10, E()))
try:
    print("deep", nest(8000, E()) == nest(8000, E()))
except RecursionError:
    print("RecursionError")
