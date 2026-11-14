# A rebound NotImplemented runs its __bool__ inside the generated __eq__.
from dataclasses import dataclass
@dataclass(frozen=True)
class K:
    a: int
H = hash(K(39))
calls = []
class T:
    def __bool__(self):
        calls.append(1)
        return len(calls) >= 2
d = {K(39): "k"}
NotImplemented = T()
print(d[H], len(calls))
