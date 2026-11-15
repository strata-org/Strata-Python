# CPython 3.12, with 100 frames below this module, runs this operation at depth 890 and raises
# RecursionError at depth 891; the model must stop with a gap at depth 891.
from typing import Union
def op():
    return Union[int, str]
def f(k):
    if k == 0:
        return op()
    return f(k - 1)
try:
    f(891)
    print('ok')
except RecursionError:
    print('RecursionError')
