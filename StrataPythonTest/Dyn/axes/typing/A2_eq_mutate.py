from dataclasses import dataclass
@dataclass
class D:
    a: object
    b: object
class E:
    def __eq__(self, o):
        print("ev E.eq")
        y.b = 99
        return True
    __hash__ = object.__hash__
    def __repr__(self):
        return 'E()'
x = D(E(), 1); y = D(E(), 1)
print(x == y, y)
