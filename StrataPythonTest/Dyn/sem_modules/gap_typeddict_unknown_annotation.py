from typing import TypedDict
class U:
    def __eq__(self, other):
        return False
    __hash__ = object.__hash__
class M(TypedDict):
    x: U()
