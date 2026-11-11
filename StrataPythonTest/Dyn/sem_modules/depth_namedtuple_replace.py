# _replace recursing through __len__ counts the frames of _replace and _make: the rules stop with
# a gap where CPython raises RecursionError.
from typing import NamedTuple
class P(NamedTuple):
    x: int
    def __len__(self):
        if self.x < 420:
            self._replace(x=self.x + 1)
        return 1
try:
    P(0)._replace(x=1)
    print("ok")
except RecursionError:
    print("RecursionError")
