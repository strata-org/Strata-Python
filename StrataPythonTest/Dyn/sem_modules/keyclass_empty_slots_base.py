# A frozen dataclass whose base has empty slots.
from dataclasses import dataclass
class B:
    __slots__ = ()
@dataclass(frozen=True)
class K(B):
    a: int
d = {K(-1): 1, K(-2): 2}
print(len(d), d[K(-2)])
