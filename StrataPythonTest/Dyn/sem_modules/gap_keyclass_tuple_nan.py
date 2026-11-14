# A compared field holding a tuple with a NaN: CPython compares the NaN by identity.
from dataclasses import dataclass, field
n1 = float("nan")
@dataclass(frozen=True)
class K:
    a: int
    b: object = field(default=None, hash=False)
d = {K(1, (n1,)): "x", K(1, (2.0,)): "y"}
print(d[K(1, (n1,))])
