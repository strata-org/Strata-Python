# An @invariant lambda with one parameter not named `self` is accepted; the parameter
# stands for the instance.
@invariant(lambda s: s.x >= 0)
class C:
    x: int
