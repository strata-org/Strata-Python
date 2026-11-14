# Two stored keys made equal to the probe after insertion: the first inserted one is found.
from dataclasses import dataclass, field
M = 2**61 - 1
@dataclass(frozen=True)
class K:
    a: int
    b: int = field(default=0, hash=False)
k1 = K(1, 1); k2 = K(1 + M, 2); k3 = K(1 + 2 * M, 3)
d = {k1: "first", k2: "second", k3: "third"}
object.__setattr__(k2, "b", 9)
object.__setattr__(k3, "b", 9)
object.__setattr__(k3, "a", 1 + M)
print(d[K(1 + M, 9)], len(d))
for i in range(50):
    d[K(10**6 + i)] = i
print(d[K(1 + M, 9)], len(d))
