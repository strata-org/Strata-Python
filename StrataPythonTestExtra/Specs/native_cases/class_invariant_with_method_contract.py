# A class-level @invariant coexists with a method-level @requires: both are
# recognized independently.
@invariant(lambda self: self.x >= 0)
class C:
    x: int

    @requires(lambda x: x >= 0)
    def m(self, x: int) -> None:
        ...
