# A property in a base class on a compared field: reading the field runs it.
from dataclasses import dataclass, field
n = [0]
class B:
    @property
    def b(self):
        n[0] += 1
        return self.__dict__.get("_b")
    @b.setter
    def b(self, v):
        self.__dict__["_b"] = v
@dataclass(frozen=True)
class K(B):
    a: int
    b: object = field(hash=False)
d = {K(-1, None): 1, K(-2, None): 2}
print(len(d), d.get(K(-3, None)), n[0])
