# CPython 3.12, with 100 frames below this module, runs this operation at depth 883 and raises
# RecursionError at depth 884; the model must stop with a gap at depth 884.
from dataclasses import dataclass
from typing import List
L = List[int]
def op():
    @dataclass
    class P:
        a: L
def f(k):
    if k == 0:
        return op()
    return f(k - 1)
try:
    f(884)
    print('ok')
except RecursionError:
    print('RecursionError')
