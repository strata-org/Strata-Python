# CPython 3.12, with 100 frames below this module, runs this operation at depth 895 and raises
# RecursionError at depth 896; the model must stop with a gap at depth 896.
from dataclasses import field
def op():
    return field(default=1)
def f(k):
    if k == 0:
        return op()
    return f(k - 1)
try:
    f(896)
    print('ok')
except RecursionError:
    print('RecursionError')
