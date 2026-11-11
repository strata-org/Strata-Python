# _replace on a subclass that defines its own _make.
from typing import NamedTuple
class P(NamedTuple):
    x: int
class Q(P):
    @classmethod
    def _make(cls, it):
        print("own make")
        return tuple.__new__(cls, it)
print(Q(1)._replace(x=2))
