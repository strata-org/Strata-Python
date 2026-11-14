# A class whose __eq__ is patched after its keys are stored: the patched __eq__ is user code.
from dataclasses import dataclass
@dataclass(frozen=True)
class J:
    a: int
d = {J(-1): 1, J(-2): 2}
J.__eq__ = lambda self, other: self.a == other.a
print(len(d), d[J(-2)])
