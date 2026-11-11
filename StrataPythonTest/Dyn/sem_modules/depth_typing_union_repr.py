# CPython raises RecursionError from depth 250 on this path; the rules count at least
# as many C levels and Python frames and stop with a gap before: the small depth
# agrees, the large one stops.
from typing import List, Optional, Union
def mk(d):
    x = int
    for _ in range(d):
        x = Optional[List[x]]
    return x
D = 100
print(len(repr(mk(D))))
D = 249
print(len(repr(mk(D))))
