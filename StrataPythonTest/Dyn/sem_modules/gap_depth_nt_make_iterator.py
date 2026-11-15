# CPython 3.12, with 100 frames below this module, runs this path 298 levels deep and raises
# RecursionError at 299; the model must stop with a gap at 299 levels.
from typing import NamedTuple
class N(NamedTuple):
    a: int
class It:
    def __init__(self, n):
        self.n = n
        self.done = False
    def __iter__(self):
        return self
    def __next__(self):
        if self.done:
            raise StopIteration
        self.done = True
        if self.n > 0:
            make(self.n - 1)
        return 1
def make(n):
    return N._make(It(n))
try:
    make(299)
    print('ok')
except RecursionError:
    print('RecursionError')
