# Frozen dataclass keys whose hashes collide: the lookup compares them, and finds the right one.
from dataclasses import dataclass, field
@dataclass(frozen=True)
class K:
    a: int
d = {K(-1): 1, K(-2): 2}
print(len(d), d[K(-1)], d[K(-2)], K(-3) in d)
d[K(-2)] = 20
print(len(d), d[K(-2)])
del d[K(-1)]
print(len(d), K(-1) in d, d[K(-2)])
