# CPython 3.12, with 100 frames below this module, runs this path 298 levels deep and raises
# RecursionError at 299; the model must stop with a gap at 299 levels.
from dataclasses import dataclass, replace
@dataclass
class R:
    n: int
    def __post_init__(self):
        if self.n > 0:
            replace(self, n=self.n - 1)
def make(n):
    return R(n)
try:
    make(299)
    print('ok')
except RecursionError:
    print('RecursionError')
