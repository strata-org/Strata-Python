# CPython 3.12, with 100 frames below this module, runs this operation at depth 855 and raises
# RecursionError at depth 856; the model must stop with a gap at depth 856.
from dataclasses import dataclass
from typing import Optional
@dataclass
class Node:
    v: int
    nxt: 'Optional[Node]'
def chain(n, v):
    x = Node(v, None)
    for _ in range(n):
        x = Node(0, x)
    return x
A = chain(20, 1); B = chain(20, 2)
def op():
    return repr(A)
def f(k):
    if k == 0:
        return op()
    return f(k - 1)
try:
    f(856)
    print('ok')
except RecursionError:
    print('RecursionError')
