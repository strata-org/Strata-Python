# Correlated branches, CORRECT program: b is flipped between the two
# ifs, so the branch that allocated A always calls the A-only method.
# The abstract fixpoint joins after the first if (x: obj:A|obj:B, no
# relation to b), so both call sites case-split and each carries an
# abort:AttributeError arm for the wrong class. Those arms are false
# at runtime; the path condition b == not b' that kills them is exactly
# what the SMT lowering can prove, so the obligations discharge there.
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


r1 = foo(True)
r2 = foo(False)
