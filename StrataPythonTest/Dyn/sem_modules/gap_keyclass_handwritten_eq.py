# A hand-written __eq__ survives the decorator, while the generated __hash__ still goes in.
from dataclasses import dataclass
@dataclass(frozen=True)
class L:
    a: int
    def __eq__(self, other):
        return self.a == other.a
print(L.__hash__ is not None)
d = {L(-1): 1, L(-2): 2}
print(len(d), d[L(-2)])
