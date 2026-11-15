# CPython 3.12, with 100 frames below this module, runs this operation at depth 894 and raises
# RecursionError at depth 895; the model must stop with a gap at depth 895.
from typing import TypedDict
def op():
    class P(TypedDict):
        a: int
        b: str
def f(k):
    if k == 0:
        return op()
    return f(k - 1)
try:
    f(895)
    print('ok')
except RecursionError:
    print('RecursionError')
