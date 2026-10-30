# An @invariant lambda with two parameters is an error that rejects the model.
@invariant(lambda self, y: True)
class C:
    x: int
