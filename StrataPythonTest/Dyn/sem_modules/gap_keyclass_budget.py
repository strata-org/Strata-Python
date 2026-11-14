# A key whose walk runs past the budget keeps the gap, although every value in it compares without
# user code: a tuple whose two members are one tuple, at each of 20 levels, is a tree of 2**20
# values.
from dataclasses import dataclass, field
@dataclass(frozen=True)
class K:
    a: int
    b: object = field(default=None, hash=False)
def make():
    t = ()
    for i in range(20):
        t = (t, t)
    return t
t = make()
d = {K(-1, t): 1, K(-2, t): 2}
print(len(d))
