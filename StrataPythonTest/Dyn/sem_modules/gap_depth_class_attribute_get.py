# CPython 3.12, with 100 frames below this module, runs this path through a class attribute's
# __get__, which dataclass calls to read a field's default, 147 levels deep and raises
# RecursionError at 148; the model must stop with a gap at 148 levels.
from dataclasses import dataclass
class Desc:
    def __init__(self, n):
        self.n = n
        self.seen = False
    def __get__(self, obj, owner):
        if not self.seen:
            self.seen = True
            if self.n > 0:
                make(self.n - 1)
        return 5
def make(n):
    @dataclass
    class P:
        a: int = Desc(n)
    return P
try:
    make(148)
    print('ok')
except RecursionError:
    print('RecursionError')
