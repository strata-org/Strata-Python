# A property on a field name decides what the generated __eq__ compares.
from dataclasses import dataclass, field
@dataclass(frozen=True)
class K:
    a: int
    b: int = field(default=0, hash=False)
d = {K(1, 1): "first", K(1, 2): "second"}
probe = K(1, 3)
K.b = property(lambda self: self.__dict__["b"])
print(len(d), probe in d)
