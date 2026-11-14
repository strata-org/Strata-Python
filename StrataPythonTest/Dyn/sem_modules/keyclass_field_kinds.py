# Colliding frozen dataclass keys with fields of each kind that compares without user code.
from dataclasses import dataclass, field
@dataclass(frozen=True)
class K:
    a: int
    b: object = field(default=None, hash=False)
pairs = [(None, 0), (True, False), (1.5, 2.5), (b"x", b"y"), (range(3), range(4)),
         ((1, "a"), (1, "b")), (int, str), (..., None)]
for x, y in pairs:
    d = {K(1, x): "x", K(1, y): "y"}
    print(len(d), d[K(1, x)], d[K(1, y)])
