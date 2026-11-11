# _make over a user iterator whose resumed __next__ calls _make again: each level costs CPython two
# Python frames, _make's and __next__'s, so the recursion passes CPython's limit.
from typing import NamedTuple
class P(NamedTuple):
    x: int
    y: int = 0
class R:
    def __init__(self, d):
        self.d = d
        self.i = 0
    def __iter__(self):
        return self
    def __next__(self):
        self.i += 1
        if self.i > 2:
            raise StopIteration
        if self.i == 2 and self.d < 520:
            P._make(R(self.d + 1))
        return self.i
try:
    print(P._make(R(0)))
except RecursionError:
    print("RecursionError")
