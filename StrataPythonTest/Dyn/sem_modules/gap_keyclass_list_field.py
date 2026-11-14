# A compared field holding a list compares its members, which may run user code.
from dataclasses import dataclass, field
n = [0]
class U:
    def __hash__(self): return 0
    def __eq__(self, other):
        n[0] += 1
        return n[0] == 3
@dataclass(frozen=True)
class K:
    a: int
    b: object = field(hash=False)
d = {K(1, [U()]): "first", K(1, [U()]): "second"}
n[0] = 0
print(d[K(1, [U()])], n[0])
