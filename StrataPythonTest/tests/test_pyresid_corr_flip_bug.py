# Correlated branches, BUGGY program: same as corr_flip_ok.py but the
# flip is missing, so every concrete run calls a method its object does
# not have. The abstract report is the same case split with the same
# abort:AttributeError arms; the difference between this file and the
# correct one is invisible at this abstraction level and surfaces
# downstream: here the SMT stage refutes the obligation and returns a
# defect witness (b=True reaches x=A calling b_only) instead of a proof.
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
    if b:
        return x.b_only()
    else:
        return x.a_only()


r1 = foo(True)
r2 = foo(False)
