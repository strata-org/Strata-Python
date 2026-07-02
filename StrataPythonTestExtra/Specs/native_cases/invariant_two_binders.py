# @invariant lambda must take exactly one `self` parameter; two binders is
# warned and the invariant is skipped.
@invariant(lambda self, y: True)
class C:
    x: int
