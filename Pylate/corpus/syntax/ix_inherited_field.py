# Interaction: field access that resolves through the MRO, which the two other
# MRO examples do not cover -- `12_inherited_mro_dispatch` and `ix_diamond_mro`
# are both method-only.
#
# `buildClassTable` unions a class's layout over its whole MRO: the annotated
# fields and every `self.f` store in every method of every class on the chain.
# So `Leaf` holds `origin` without declaring it, and a store through a receiver
# other than `self` reaches it without an `attr-missing` obligation.
#
# A subclass that defines `__init__` either assigns the inherited field itself,
# as `Leaf` does here, or delegates with `super().__init__(..)`, which
# `ix_super_dispatch.py` covers. `Middle` defines no `__init__` and inherits one.


class Base:
    def __init__(self, origin: int) -> None:
        self.origin: int = origin

    def read_origin(self) -> int:
        return self.origin


class Middle(Base):
    def doubled(self) -> int:
        return self.origin * 2


class Leaf(Middle):
    def __init__(self) -> None:
        self.origin: int = 5
        self.own: int = 7

    def total(self) -> int:
        return self.origin + self.own


def through_self() -> int:
    leaf = Leaf()
    return leaf.total() + leaf.doubled() + leaf.read_origin()


def through_other_receiver() -> int:
    leaf = Leaf()
    leaf.origin = 11
    return leaf.origin + leaf.doubled()


def inherited_without_own_init(origin: int) -> int:
    middle = Middle(origin)
    middle.origin = origin + 1
    return middle.read_origin()


# Diamond: the field is declared once on the shared base and reached from the
# bottom, so the layout union has to survive the C3 merge rather than one chain.
class DiaLeft(Base):
    def left_view(self) -> int:
        return self.origin + 1


class DiaRight(Base):
    def right_view(self) -> int:
        return self.origin + 2


class Bottom(DiaLeft, DiaRight):
    def __init__(self) -> None:
        self.origin: int = 3


def diamond_field() -> int:
    bottom = Bottom()
    return bottom.left_view() + bottom.right_view() + bottom.origin
