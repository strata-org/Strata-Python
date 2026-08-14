@invariant(lambda self: self.a >= self.b)
class CGe:
    a: int
    b: int


@invariant(lambda self: self.a <= self.b)
class CLe:
    a: int
    b: int
