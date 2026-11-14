from dataclasses import dataclass
@dataclass
class D:
    a: object
    b: object
class R:
    def __repr__(self):
        d.b = 'changed'
        return 'R()'
d = D(R(), 1)
print(repr(d))
