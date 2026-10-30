# An @invariant lambda without a parameter is an error that rejects the model.
@invariant(lambda: True)
class C:
    x: int
