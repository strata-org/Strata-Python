# CPython 3.12, with 100 frames below this module, runs Optional[X] of a 60-level typing alias at
# depth 829 and raises RecursionError at depth 830, inside the hashes of the union's deduplication;
# the model must stop with a gap at depth 830.
from typing import List, Optional
X = int
for _ in range(60):
    X = List[X]
def op():
    return Optional[X]
def f(k):
    if k == 0:
        return op()
    return f(k - 1)
try:
    f(830)
    print('ok')
except RecursionError:
    print('RecursionError')
