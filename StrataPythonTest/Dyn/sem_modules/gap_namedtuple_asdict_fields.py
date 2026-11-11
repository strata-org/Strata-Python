# _asdict reads self._fields, which a subclass may make a list.
from typing import NamedTuple
class P(NamedTuple):
    x: int
class Q(P):
    _fields = ["x"]
print(Q(1)._asdict())
