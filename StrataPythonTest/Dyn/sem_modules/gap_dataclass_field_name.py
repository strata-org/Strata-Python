# A field name that the generated source can't take.
from dataclasses import dataclass
@dataclass
class C:
    x: int
    __annotations__["a b"] = int
print(C(1, 2))
