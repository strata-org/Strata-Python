# A __getattr__ on a colliding dataclass key: the lookup keeps its gap.
from dataclasses import dataclass, field
@dataclass(frozen=True)
class K:
    a: int
    def __getattr__(self, name):
        return 0
d = {K(-1): 1, K(-2): 2}
print(len(d))
