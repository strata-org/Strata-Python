# _replace on a class whose _make is not the named tuple's.
from typing import NamedTuple
class P(NamedTuple):
    x: int
    y: int = 0
class R(NamedTuple):
    a: int
class Q(P):
    _make = R._make
print(Q(1, 2)._replace(x=5))
