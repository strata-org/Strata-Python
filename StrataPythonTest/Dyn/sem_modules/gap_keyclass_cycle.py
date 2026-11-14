# A key that holds itself through a compared field, colliding with another key.
from dataclasses import dataclass, field
M = 2**61 - 1
@dataclass(frozen=True)
class K:
    a: int
    b: object = field(default=None, hash=False)
k = K(1)
object.__setattr__(k, "b", k)
d = {k: "x"}
try:
    print(K(1 + M) in d)
except RecursionError:
    print("RecursionError")
j = K(1)
object.__setattr__(j, "b", j)
try:
    print(j in d)
except RecursionError:
    print("RecursionError")
