# @invariant lambda binder must be `self`; a differently-named binder is warned
# and the invariant is skipped.
@invariant(lambda s: s.x >= 0)
class C:
    x: int
