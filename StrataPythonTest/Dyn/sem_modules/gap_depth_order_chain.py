# CPython 3.12, with 100 frames below this module, runs this operation at depth 876 and raises
# RecursionError at depth 877; the model must stop with a gap at depth 877.
from dataclasses import dataclass
from typing import Optional
@dataclass(order=True)
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
    return A < B
def f(k):
    if k == 0:
        return op()
    return f(k - 1)
try:
    f(877)
    print('ok')
except RecursionError:
    print('RecursionError')
