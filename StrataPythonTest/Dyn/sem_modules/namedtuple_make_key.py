# _make as the key of sorted, max and min over user iterators: the key calls suspend inside the
# outer walks.
from typing import NamedTuple
class P(NamedTuple):
    x: int
    y: int = 0
class C:
    def __init__(self, a, b):
        self.v = [a, b]
        self.i = 0
    def __iter__(self):
        return self
    def __next__(self):
        if self.i == 2:
            raise StopIteration
        self.i += 1
        print("next", self.v[self.i - 1])
        return self.v[self.i - 1]
for c in sorted([C(3, 1), C(1, 2), C(2, 0)], key=P._make):
    print(c.v)
print(max([C(3, 1), C(1, 2)], key=P._make).v)
print(min([C(3, 1), C(1, 2)], key=P._make).v)
