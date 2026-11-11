# The accessors and the generated methods on plain tuples and on other named tuples.
from typing import NamedTuple
class P(NamedTuple):
    x: int
    y: int = 0
print(P.x.__get__((5, 6)))
class Q(NamedTuple):
    a: int
print(P.x.__get__(Q(3)))
try:
    print(P.y.__get__(Q(3)))
except IndexError as e:
    print("IndexError:", e)
print(P.__repr__((1, 2)))
print(P.__getnewargs__((1, 2)))
