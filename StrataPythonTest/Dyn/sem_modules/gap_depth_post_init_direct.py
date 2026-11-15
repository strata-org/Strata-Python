# CPython 3.12, with 100 frames below this module, runs this path 448 levels deep and raises
# RecursionError at 449; the model must stop with a gap at 449 levels.
from dataclasses import dataclass
@dataclass
class R:
    n: int
    def __post_init__(self):
        if self.n > 0:
            R(self.n - 1)
def make(n):
    return R(n)
try:
    make(449)
    print('ok')
except RecursionError:
    print('RecursionError')
