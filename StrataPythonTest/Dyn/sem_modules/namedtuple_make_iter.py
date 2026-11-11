# _make over iterables other than a tuple or a list: tuple.__new__ walks them, and a user
# iterator's __next__ runs as Python code.
from typing import NamedTuple


class P(NamedTuple):
    x: int
    y: int = 0


class Count:
    def __init__(self, n):
        self.i = 0
        self.n = n

    def __iter__(self):
        return self

    def __next__(self):
        if self.i == self.n:
            raise StopIteration
        self.i += 1
        print("next", self.i)
        return self.i


print(P._make(range(2)))
print(P._make(iter([5, 6])))
print(P._make(Count(2)))
print(P._make("ab"))
print(P._make({1: 2, 3: 4}))
for it in (Count(3), Count(1), range(0)):
    try:
        P._make(it)
    except TypeError as e:
        print("TypeError:", e)


class Bad:
    def __iter__(self):
        return self

    def __next__(self):
        raise ValueError("boom")


try:
    P._make(Bad())
except ValueError as e:
    print("ValueError:", e)
try:
    P._make(5)
except TypeError as e:
    print("TypeError:", e)
print(type(P._make(Count(2))) is P, P._make(Count(2)).x)
