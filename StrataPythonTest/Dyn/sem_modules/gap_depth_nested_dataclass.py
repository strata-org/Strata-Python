# CPython 3.12, with 100 frames below this module, runs this path 126 levels deep and raises
# RecursionError at 127; the model must stop with a gap at 127 levels.
from dataclasses import dataclass
class D:
    def __init__(self, n):
        self.n = n
    def __repr__(self):
        if self.n > 0:
            make(self.n - 1)
        return 'D'
def make(n):
    @dataclass
    class P:
        a: object = D(n)
    return P
try:
    make(127)
    print('ok')
except RecursionError:
    print('RecursionError')
