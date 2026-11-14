# Generated __eq__ with a hand-written __hash__ on a frozen dataclass.
from dataclasses import dataclass
@dataclass(frozen=True)
class K:
    a: int
    def __hash__(self):
        return 0
d = {K(1): 1, K(2): 2}
print(len(d), d[K(2)], K(3) in d)
