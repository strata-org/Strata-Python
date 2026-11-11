# A typing cache that holds a deeply nested key: a later subscription, called deep in the stack,
# could collide with that key's hash, and CPython's comparison would then hash the key again.
from typing import List

t = int
for _ in range(700):
    t = List[t]


def deep(n):
    if n == 0:
        return List[str]
    return deep(n - 1)


print(List[str] is List[str])
print(deep(300) is List[str])
