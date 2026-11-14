# Two keys with one str hash term and an unhashed compared field.
from dataclasses import dataclass, field
@dataclass(frozen=True)
class S:
    a: str
    b: int = field(default=0, hash=False)
d = {S("a", 1): 1, S("a", 2): 2}
print(len(d), d[S("a", 1)], d[S("a", 2)])
