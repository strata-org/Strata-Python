"""A subclass `__init__` that leaves an inherited field uninitialized.

A subclass defining `__init__` must initialize the fields it inherits, either by
assigning them or by delegating with `super().__init__(..)`. This one does
neither: the field is in the layout -- the union runs over the MRO -- but no path
initializes it, and CPython raises `AttributeError` on the read. The analyzer must report `init-missing` at the
class and `uninit-field` at the read rather than answering with a value.

This is the case that decides whether the "is the field initialized anywhere on
the hierarchy" question is answered precisely, and it is answered by the
abstract interpreter rather than by the admission check, which cannot know a
receiver's class.
"""


class Base:
    def __init__(self, origin: int) -> None:
        self.origin: int = origin


class Forgetful(Base):
    def __init__(self) -> None:
        self.own: int = 1


def read_uninitialized() -> int:
    obj = Forgetful()
    return obj.origin
