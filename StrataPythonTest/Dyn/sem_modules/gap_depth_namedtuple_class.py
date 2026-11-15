# CPython 3.12, with 100 frames below this module, runs this operation at depth 893 and raises
# RecursionError at depth 894; the model must stop with a gap at depth 894.
from typing import NamedTuple
def op():
    class P(NamedTuple):
        a: int
        b: str = 'x'
def f(k):
    if k == 0:
        return op()
    return f(k - 1)
try:
    f(894)
    print('ok')
except RecursionError:
    print('RecursionError')
