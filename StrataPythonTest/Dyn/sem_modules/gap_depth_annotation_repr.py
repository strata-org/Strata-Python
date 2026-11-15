# CPython 3.12, with 100 frames below this module, runs this path through an annotation's __repr__,
# which dataclass calls to build the class's __doc__, 110 levels deep and raises RecursionError at
# 111; the model must stop with a gap at 111 levels.
from dataclasses import dataclass
class A:
    def __init__(self, n):
        self.n = n
    def __repr__(self):
        if self.n > 0:
            make(self.n - 1)
        return 'A'
def make(n):
    @dataclass
    class P:
        a: A(n)
    return P
try:
    make(111)
    print('ok')
except RecursionError:
    print('RecursionError')
