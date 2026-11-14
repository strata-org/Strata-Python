# A frozen dataclass that subclasses tuple: tuple.__eq__ compares its items, which aren't fields.
from dataclasses import dataclass
M = 2**61 - 1
n = [0]
class U:
    def __hash__(self): return 0
    def __eq__(self, other):
        n[0] += 1
        return n[0] == 3
@dataclass(frozen=True)
class K(tuple):
    "A docstring, so that the decorator writes none."
    a: int = 1
    def __new__(cls, a=1):
        return tuple.__new__(cls, (U(),))
d = {(1,): "A", (1 + M,): "B"}
n[0] = 0
print(d[K(1)], n[0])
