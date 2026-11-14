# A str key in the same dict: its symbolic hash may collide, so the lookup is off the exact branch.
from dataclasses import dataclass
@dataclass(frozen=True)
class K:
    a: int
d = {"x": 0, K(-1): 1, K(-2): 2}
print(len(d), d[K(-2)])
