from dataclasses import dataclass
from typing import NamedTuple, TypedDict
class I(int):
    def __eq__(self, o):
        print("ev I.eq")
        return False
    def __lt__(self, o):
        print("ev I.lt")
        return True
    def __hash__(self):
        print("ev I.hash")
        return 5
    def __repr__(self):
        return 'I!'
class S(str):
    def __eq__(self, o):
        print("ev S.eq")
        return True
    __hash__ = str.__hash__
    def __repr__(self):
        return 'S!'
@dataclass(order=True, frozen=True)
class D:
    a: int
    b: object = 'x'
x = I(1)
print(D(x) == D(x), D(I(1)) == D(I(1)), D(I(1)) < D(I(1)), hash(D(I(1), 3)) == hash((5, 3)), repr(D(I(1), S('q'))))
print(D(1, S('a')) == D(1, 'b'))
class P(NamedTuple):
    a: int
print(P(I(1)) == P(I(1)), repr(P(I(1))), P(I(1)) < P(I(2)))
class TD(TypedDict):
    a: int
print(TD(a=I(1)) == {'a': I(1)}, repr(TD(a=I(1))))
