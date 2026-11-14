# An int key of a str's hash in an instance's own __dict__.
from dataclasses import dataclass
@dataclass(frozen=True)
class K:
    a: int
k = K(-1)
k.__dict__[hash("x")] = "h"
d = {k: 1, K(-2): 2}
print(len(d))
