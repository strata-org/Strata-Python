from typing import NamedTuple
class P(NamedTuple):
    x: object
    y: object
class E:
    def __eq__(self, o):
        print("ev eq")
        return True
    __hash__ = object.__hash__
print(P(E(), [1]) == P(E(), [1]))
