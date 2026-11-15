# CPython 3.12, with 100 frames below this module, runs this path 299 levels deep and raises
# RecursionError at 300; the model must stop with a gap at 300 levels.
from dataclasses import dataclass, field
cnt = [0]
@dataclass
class N:
    k: int = 0
    nxt: object = field(default_factory=lambda: mk())
def mk():
    if cnt[0] == 0:
        return None
    cnt[0] -= 1
    return N()
def make(n):
    cnt[0] = n
    return mk()
try:
    make(300)
    print('ok')
except RecursionError:
    print('RecursionError')
