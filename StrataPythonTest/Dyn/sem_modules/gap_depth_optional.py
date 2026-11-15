# CPython 3.12, with 100 frames below this module, runs this operation at depth 887 and raises
# RecursionError at depth 888; the model must stop with a gap at depth 888.
from typing import Optional
def op():
    return Optional[int]
def f(k):
    if k == 0:
        return op()
    return f(k - 1)
try:
    f(888)
    print('ok')
except RecursionError:
    print('RecursionError')
