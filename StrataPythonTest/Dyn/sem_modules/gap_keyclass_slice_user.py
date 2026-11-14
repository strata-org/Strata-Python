# A compared field holding a slice with a user object, whose __eq__ answers true on its third call.
from dataclasses import dataclass, field
n = [0]
class U:
    def __hash__(self): return 0
    def __eq__(self, other):
        n[0] += 1
        return n[0] == 3
class G:
    def __getitem__(self, k):
        return k
g = G()
@dataclass(frozen=True)
class K:
    a: int
    b: object = field(hash=False)
d = {K(1, g[U():2]): "first", K(1, g[U():2]): "second"}
n[0] = 0
print(d[K(1, g[U():2])], n[0])
