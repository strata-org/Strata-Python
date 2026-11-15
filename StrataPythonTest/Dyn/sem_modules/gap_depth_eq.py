# CPython 3.12, with 100 frames below this module, runs this operation at depth 896 and raises
# RecursionError at depth 897; the model must stop with a gap at depth 897.
from dataclasses import dataclass
@dataclass
class P:
    a: int
X = P(1); Y = P(2)
def op():
    return X == Y
def f(k):
    if k == 0:
        return op()
    return f(k - 1)
try:
    f(897)
    print('ok')
except RecursionError:
    print('RecursionError')
