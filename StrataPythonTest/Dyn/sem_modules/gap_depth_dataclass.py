# CPython 3.12, with 100 frames below this module, runs this operation at depth 885 and raises
# RecursionError at depth 886; the model must stop with a gap at depth 886.
from dataclasses import dataclass
def op():
    @dataclass
    class P:
        a: int
        b: str = 'x'
def f(k):
    if k == 0:
        return op()
    return f(k - 1)
try:
    f(886)
    print('ok')
except RecursionError:
    print('RecursionError')
