# A class attribute under a compared field holds a large shared tuple: the object's own __dict__
# wins over it, so its contents are never compared, and the lookup answers.
from dataclasses import dataclass, field
@dataclass(frozen=True)
class K:
    a: int
    b: int = field(default=0, hash=False)
def make(n):
    t = ()
    for i in range(n):
        t = (t, t)
    return t
d = {K(-1, 1): 1}
K.b = make(20)
d[K(-2, 2)] = 2
print(len(d), d[K(-1, 1)], d[K(-2, 2)])
