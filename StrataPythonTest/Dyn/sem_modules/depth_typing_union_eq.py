# CPython raises RecursionError from a recursion of depth 797 around this use of a value
# built deep; the rules count at least as many Python frames and stop with a gap
# before: the small depth agrees, the large one stops.
from typing import List, Optional, Union
def mk2(d):
    x = int
    for _ in range(d):
        x = Union[List[x], None]
    return x
def mk(d):
    x = int
    for _ in range(d):
        x = Optional[List[x]]
    return x
A = mk(100)
C = mk2(100)
def deep(n):
    if n == 0:
        return A == C
    return deep(n - 1)
D = 10
print(deep(D))
D = 796
print(deep(D))
