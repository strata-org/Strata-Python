# CPython raises RecursionError from depth 997 on this path; the rules count at least
# as many C levels and Python frames and stop with a gap before: the small depth
# agrees, the large one stops.
from typing import List, Optional, Union
def mk(d):
    x = int
    for _ in range(d):
        x = List[x]
    return x
D = 300
mk(D)
print(1)
D = 996
mk(D)
print(1)
