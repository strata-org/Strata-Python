# __post_init__, inheritance and replace.
from dataclasses import dataclass, replace, field
@dataclass
class P:
    x: int
    y: int = 0
    def __post_init__(self):
        self.s = self.x + self.y
print(P(1, 2).s)
@dataclass(frozen=True)
class Key:
    value: int
k = Key(1)
r = replace(k, value=2)
print(k, r, k == Key(1), k == r)
try:
    replace(k, z=1)
except TypeError as e:
    print("TypeError:", e)
try:
    replace(1, value=2)
except TypeError as e:
    print("TypeError:", e)
@dataclass
class N:
    a: int
    b: int = field(init=False, default=5)
try:
    replace(N(1), b=2)
except ValueError as e:
    print("ValueError:", e)
print(replace(N(1)))
