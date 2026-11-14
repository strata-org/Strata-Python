# Colliding keys with slice fields made by subscription.
from dataclasses import dataclass, field
class G:
    def __getitem__(self, k):
        return k
g = G()
@dataclass(frozen=True)
class K:
    a: int
    b: object = field(default=None, hash=False)
d = {K(1, g[1:2]): "x", K(1, g[1:3]): "y"}
print(len(d), d[K(1, g[1:2])], d[K(1, g[1:3])])
