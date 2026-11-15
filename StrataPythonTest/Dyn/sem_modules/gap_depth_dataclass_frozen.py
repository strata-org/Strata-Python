# CPython 3.12, with 100 frames below this module, runs this operation at depth 886 and raises
# RecursionError at depth 887; the model must stop with a gap at depth 887.
from dataclasses import dataclass
def op():
    @dataclass(frozen=True)
    class P:
        a: int
def f(k):
    if k == 0:
        return op()
    return f(k - 1)
try:
    f(887)
    print('ok')
except RecursionError:
    print('RecursionError')
