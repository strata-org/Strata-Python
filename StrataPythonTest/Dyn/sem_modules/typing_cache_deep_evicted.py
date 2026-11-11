# A deeply nested key leaves the typing cache after 128 other subscriptions; then a subscription
# deep in the stack no longer counts a comparison with it.
from typing import List

t = int
for _ in range(700):
    t = List[t]
for i in range(128):
    List[i]


def deep(n):
    if n == 0:
        return List[str]
    return deep(n - 1)


print(List[str] is List[str])
print(deep(300) is List[str])
