# A compared field deleted with object.__delattr__: the comparison reads the class default.
from dataclasses import dataclass, field
@dataclass(frozen=True)
class K:
    a: int
    b: int = field(default=0, hash=False)
k = K(1, 5)
object.__delattr__(k, "b")
d = {k: "first", K(1, 7): "second"}
print(len(d), d[K(1, 0)])
