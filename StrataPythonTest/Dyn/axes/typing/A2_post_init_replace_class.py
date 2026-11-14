from dataclasses import dataclass
@dataclass
class D:
    a: int
    def __post_init__(self):
        D.__repr__ = lambda self: 'patched'
d = D(1)
print(repr(d), repr(D(2)))
