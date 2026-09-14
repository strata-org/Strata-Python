# The corr_flip program under the eafp preset (picked from the _eafp
# suffix): AttributeError is dispatch-category, so it still aborts even
# under eafp; the point is that relaxing key/value does not relax
# dispatch integrity.
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
    b = not b
    if b:
        return x.b_only()
    else:
        return x.a_only()


r = foo(True)
