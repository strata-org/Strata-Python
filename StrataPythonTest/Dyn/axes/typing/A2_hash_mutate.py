from dataclasses import dataclass
@dataclass(unsafe_hash=True)
class D:
    a: object
    b: object
class H:
    def __hash__(self):
        d.b = 2
        return 7
d = D(H(), 1)
print(hash(d) == hash((7, 1)), hash(d) == hash((7, 2)))
