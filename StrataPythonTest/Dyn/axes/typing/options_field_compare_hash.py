from dataclasses import dataclass, field
@dataclass(unsafe_hash=True)
class D:
    a: int = field(default=1, compare=False)
    b: int = field(default=2, hash=False)
    c: int = field(default=3, compare=True, hash=None)
print(D(1) == D(9), hash(D(1, 2, 3)) == hash((3,)), hash(D(1, 7, 3)) == hash(D(1, 8, 3)))
