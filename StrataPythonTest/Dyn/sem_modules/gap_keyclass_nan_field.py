# A NaN in a compared field: CPython compares it by identity inside the tuple.
from dataclasses import dataclass, field
n1 = float("nan")
@dataclass(frozen=True)
class K:
    a: int
    b: float = field(default=0.0, hash=False)
d = {K(1, n1): "x", K(1, 2.0): "y"}
print(d[K(1, n1)])
