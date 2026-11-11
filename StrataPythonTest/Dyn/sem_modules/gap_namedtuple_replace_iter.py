# _replace on a named tuple whose class overrides __iter__.
from typing import NamedTuple
class P(NamedTuple):
    x: int
    def __iter__(self):
        print("iter")
        return iter((9,))
p = P(1)
a, = p
print(a)
print(p._replace(x=2))
