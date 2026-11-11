from typing import NamedTuple
class U:
    def __eq__(self, other):
        return False
    __hash__ = object.__hash__
class P(NamedTuple):
    x: U()
