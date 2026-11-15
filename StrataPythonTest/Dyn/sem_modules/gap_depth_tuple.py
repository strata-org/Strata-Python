# CPython 3.12, with 100 frames below this module, runs this operation at depth 890 and raises
# RecursionError at depth 891; the model must stop with a gap at depth 891.
from typing import Tuple
def op():
    return Tuple[int, ...]
def f(k):
    if k == 0:
        return op()
    return f(k - 1)
try:
    f(891)
    print('ok')
except RecursionError:
    print('RecursionError')
