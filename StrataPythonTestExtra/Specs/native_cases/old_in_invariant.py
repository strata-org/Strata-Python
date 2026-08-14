# A class invariant decorator is not a two-state predicate.
@invariant(lambda self: OLD(self.x) >= 0)
class C:
    x: int
