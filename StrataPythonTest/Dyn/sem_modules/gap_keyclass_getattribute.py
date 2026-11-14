# A __getattribute__ runs on every field read of the generated __eq__.
from dataclasses import dataclass, field
n = [0]
@dataclass(frozen=True)
class K:
    a: int
    b: int = field(default=0, hash=False)
    def __getattribute__(self, name):
        if name == "b":
            n[0] += 1
        return object.__getattribute__(self, name)
d = {K(1, 1): "first", K(1, 2): "second"}
n[0] = 0
print(K(1, 3) in d, n[0] > 0)
