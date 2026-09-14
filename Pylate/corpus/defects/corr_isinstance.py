# Correlated branches, RESOLVED IN THE FIXPOINT: the same A/B setup,
# but the second dispatch is guarded by isinstance instead of a boolean
# whose correlation the domain cannot see. refine() prunes x's tags in
# each branch, both call sites devirtualize to a single class, and no
# abort arm exists: this is the shape the analysis proves by itself,
# with nothing left for the SMT stage.
class A:
    def a_only(self) -> str:
        return "a"


class B:
    def b_only(self) -> int:
        return 1


def foo(b: bool):
    if b:
        x = A()
    else:
        x = B()
    if isinstance(x, A):
        return x.a_only()
    else:
        return x.b_only()


r1 = foo(True)
r2 = foo(False)
