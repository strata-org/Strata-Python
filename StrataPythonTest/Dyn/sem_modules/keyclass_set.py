# A set of colliding frozen dataclass keys, after a discard makes its layout inexact: each add
# compares the new key with one stored key.
from dataclasses import dataclass
@dataclass(frozen=True)
class K:
    a: int
s = {"x"}
s.discard("x")
s.add(K(-1))
s.add(K(-2))
print(len(s))
