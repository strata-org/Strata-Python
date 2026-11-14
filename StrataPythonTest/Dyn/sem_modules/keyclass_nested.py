# Colliding keys that hold another frozen dataclass, and keys of an unsafe_hash class.
from dataclasses import dataclass, field
@dataclass(frozen=True)
class P:
    x: int
@dataclass(frozen=True)
class K:
    a: int
    p: P = field(hash=False)
d = {K(1, P(1)): 1, K(1, P(2)): 2}
print(len(d), d[K(1, P(1))], d[K(1, P(2))], K(1, P(3)) in d)
@dataclass(unsafe_hash=True)
class U:
    a: int
    b: int = field(default=0, hash=False)
e = {U(1, 1): 1, U(1, 2): 2}
print(len(e), e[U(1, 2)])
