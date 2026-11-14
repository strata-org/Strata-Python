# builtins.NotImplemented rebound to an object with a __bool__.
import builtins
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
builtins.NotImplemented = T()
print(d[H], len(calls))
