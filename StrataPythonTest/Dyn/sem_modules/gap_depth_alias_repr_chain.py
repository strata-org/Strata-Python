# CPython 3.12, with 100 frames below this module, runs this operation at depth 857 and raises
# RecursionError at depth 858; the model must stop with a gap at depth 858.
from typing import List
T = int
for _ in range(20):
    T = List[T]
def op():
    return repr(T)
def f(k):
    if k == 0:
        return op()
    return f(k - 1)
try:
    f(858)
    print('ok')
except RecursionError:
    print('RecursionError')
