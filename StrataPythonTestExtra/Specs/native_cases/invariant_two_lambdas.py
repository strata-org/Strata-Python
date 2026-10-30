# An @invariant with two lambdas is an error: one decorator states one invariant.
@invariant(lambda self: self.x >= 0, lambda self: self.x < 9)
class C:
    x: int
