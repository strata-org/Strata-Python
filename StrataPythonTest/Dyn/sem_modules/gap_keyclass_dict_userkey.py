# A user key in an instance's own __dict__ makes the field read run user code.
from dataclasses import dataclass
class U:
    def __hash__(self): return 0
    def __eq__(self, other): return False
@dataclass(frozen=True)
class K:
    a: int
k = K(-1)
k.__dict__[U()] = "x"
d = {k: 1, K(-2): 2}
print(len(d))
