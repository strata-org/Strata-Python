# The repr of a named tuple whose class name is not a str.
from typing import NamedTuple
class P(NamedTuple):
    x: int
class Fake:
    pass
f = Fake()
f.__name__ = "Zed"
class Q(P):
    @property
    def __class__(self):
        return f
print(repr(Q(1)))
f.__name__ = 5
try:
    print(repr(Q(1)))
except TypeError as e:
    print("TypeError:", e)
