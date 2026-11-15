# CPython 3.12, with 100 frames below this module, runs this path through a Field default's
# __set_name__, which the class statement calls, 295 levels deep and raises RecursionError at 296;
# the model must stop with a gap at 296 levels.
from dataclasses import dataclass, field
class SN:
    def __init__(self, n):
        self.n = n
    def __repr__(self):
        return 'SN'
    def __set_name__(self, owner, name):
        if self.n > 0:
            make(self.n - 1)
def make(n):
    @dataclass
    class P:
        a: object = field(default=SN(n))
    return P
try:
    make(296)
    print('ok')
except RecursionError:
    print('RecursionError')
