# CPython 3.12, with 100 frames below this module, runs this operation at depth 896 and raises
# RecursionError at depth 897; the model must stop with a gap at depth 897.
from typing import NamedTuple
class N(NamedTuple):
    a: int
X = N(1)
def op():
    return repr(X)
def f(k):
    if k == 0:
        return op()
    return f(k - 1)
try:
    f(897)
    print('ok')
except RecursionError:
    print('RecursionError')
