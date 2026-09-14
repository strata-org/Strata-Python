# Interaction: `__slots__` as a shape declaration, and what it licenses.
#
# A class that is slots-complete over its whole MRO has no `__dict__`, so CPython
# itself refuses a store outside the layout. That turns an obligation into a
# guaranteed error, which is why `__slots__` is admitted in a class body at all.
#
# Measured, and the reason the check is MRO-wide rather than per class: a subclass
# that declares nothing gets a `__dict__` back and `o.zz = 5` is allowed again,
# while `__slots__ = ()` keeps the guarantee. `defects/slots_shape_stores.py` has
# both store cases.


class Point:
    __slots__ = ("x", "y")

    def __init__(self) -> None:
        self.x: int = 0
        self.y: int = 0

    def shifted(self) -> int:
        return self.x + self.y


class Point3(Point):
    __slots__ = ("z",)

    def __init__(self) -> None:
        self.x: int = 0
        self.y: int = 0
        self.z: int = 0

    def volume(self) -> int:
        return self.x + self.y + self.z


# `__slots__ = ()` adds no field and keeps the chain complete.
class Tagged(Point):
    __slots__ = ()

    def doubled(self) -> int:
        return self.x * 2


def stores_within_the_layout() -> int:
    p = Point()
    p.x = 3
    p.y = 4
    return p.shifted()


def inherited_slot_through_receiver() -> int:
    t = Tagged()
    t.x = 5
    return t.doubled()


def own_and_inherited_slots() -> int:
    q = Point3()
    q.z = 2
    return q.volume()
