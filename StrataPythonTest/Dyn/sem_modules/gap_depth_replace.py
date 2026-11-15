# CPython 3.12, with 100 frames below this module, runs this operation at depth 895 and raises
# RecursionError at depth 896; the model must stop with a gap at depth 896.
from dataclasses import dataclass, replace
@dataclass
class P:
    a: int
X = P(1)
def op():
    return replace(X, a=2)
def f(k):
    if k == 0:
        return op()
    return f(k - 1)
try:
    f(896)
    print('ok')
except RecursionError:
    print('RecursionError')
