from dataclasses import dataclass
depth = [0]
@dataclass
class D:
    a: object
class E:
    def __eq__(self, o):
        depth[0] += 1
        if depth[0] < 3:
            return D(E()) == D(E())
        return False
    __hash__ = object.__hash__
print(D(E()) == D(E()), depth)
