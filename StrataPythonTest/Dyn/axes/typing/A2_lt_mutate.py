from dataclasses import dataclass
@dataclass(order=True)
class D:
    a: object
    b: object
class N:
    def __init__(self, v): self.v = v
    def __eq__(self, o):
        y.b = -5
        return self.v == o.v
    def __lt__(self, o):
        return self.v < o.v
    __hash__ = object.__hash__
    def __repr__(self): return 'N()'
x = D(N(1), 1); y = D(N(1), 2)
print(x < y, y.b)
