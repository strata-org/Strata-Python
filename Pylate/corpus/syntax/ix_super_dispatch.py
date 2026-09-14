# Interaction: zero-argument `super()`, whose target depends on the *receiver's*
# class rather than the class the call is written in.
#
# `Left.m` and `Right.m` each delegate upward. For a `Left` receiver that reaches
# `Base.m`; for a `Bottom` receiver it reaches `Right.m`, because C3 puts `Right`
# between `Left` and `Base` on `Bottom`'s MRO. Resolving against `Left`'s own base
# would give `Base` in both cases and silently skip `Right`. Verified against
# CPython: `Left().m()` is 11 and `Bottom().m()` is 111.
#
# So the site is an ordinary per-tag dispatch with one arm per candidate class,
# and the log shows `obj:Left->Base.m after Left | obj:Bottom->Right.m after Left`.


class Base:
    def __init__(self, origin: int) -> None:
        self.origin: int = origin

    def m(self) -> int:
        return 1


class Left(Base):
    def m(self) -> int:
        return 10 + super().m()


class Right(Base):
    def m(self) -> int:
        return 100 + super().m()


class Bottom(Left, Right):
    pass


def cooperative_left() -> int:
    return Left(0).m()


def cooperative_bottom() -> int:
    return Bottom(0).m()


# Constructor delegation: the inherited field is initialized by the base's
# `__init__`, reached through `super()`. `checkInitializedFields` reads the heap
# after construction rather than the subclass body, so delegating this way
# discharges the obligation that `defects/inherited_field_uninitialized.py`
# reports when a subclass neither delegates nor assigns the field itself.
class Delegating(Base):
    def __init__(self) -> None:
        super().__init__(3)
        self.own: int = 1

    def total(self) -> int:
        return self.origin + self.own


def delegated_init() -> int:
    return Delegating().total()


# No user class follows `Solo` on its MRO, so `super().__init__()` reaches
# `object.__init__`, which takes no arguments and does nothing.
class Solo:
    def __init__(self) -> None:
        super().__init__()
        self.n: int = 1


def object_init_is_inert() -> int:
    return Solo().n
