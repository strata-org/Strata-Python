# A compared field holding a tuple with a user object, whose __eq__ answers true on its third call.
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
d = {K(1, (U(),)): "first", K(1, (U(),)): "second"}
n[0] = 0
print(d[K(1, (U(),))], n[0])
