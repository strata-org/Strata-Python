# CPython raises RecursionError from a recursion of depth 697 around this use of a value
# built deep; the rules count at least as many Python frames and stop with a gap
# before: the small depth agrees, the large one stops.
from typing import List, Optional, Union
def mk(d):
    x = int
    for _ in range(d):
        x = List[x]
    return x
A = mk(300)
def deep(n):
    if n == 0:
        return {A: 1}[A]
    return deep(n - 1)
D = 10
print(deep(D))
D = 696
print(deep(D))
