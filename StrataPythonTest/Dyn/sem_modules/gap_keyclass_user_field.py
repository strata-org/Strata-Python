# A colliding key whose compared field holds a user object: its __eq__ runs, so after a false
# comparison the lookup gaps.
from dataclasses import dataclass, field
class U:
    def __hash__(self): return 0
    def __eq__(self, other): return False
@dataclass(frozen=True)
class K:
    a: int
    b: object = field(hash=False)
d = {K(1, 1): "first", K(1, 2): "second"}
print(len(d), K(1, U()) in d)
