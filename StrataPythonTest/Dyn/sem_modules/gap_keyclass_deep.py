# A chain of keys deeper than the walk follows: the lookup keeps its gap.
from dataclasses import dataclass, field
M = 2**61 - 1
@dataclass(frozen=True)
class K:
    a: int
    b: object = field(default=None, hash=False)
t = None
for i in range(1000):
    t = K(i, t)
d = {K(1, t): "x", K(1 + M, t): "y"}
print(len(d))
