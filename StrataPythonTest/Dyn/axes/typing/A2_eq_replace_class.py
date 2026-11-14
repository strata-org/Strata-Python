from dataclasses import dataclass
@dataclass
class D:
    a: object
    b: object
class E:
    def __eq__(self, o):
        D.__eq__ = lambda s, o: 'patched'
        return True
    __hash__ = object.__hash__
x = D(E(), 1); y = D(E(), 1)
print(x == y, x == y)
