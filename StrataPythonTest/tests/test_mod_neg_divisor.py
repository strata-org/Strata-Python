# Python's `%` takes the sign of the DIVISOR. Regression test for the
# Euclidean-modulo soundness bug (Strata used to compute 1 here).
def test() -> None:
    x: int = 7 % (-2)
    assert x == -1, "modulo takes the sign of the divisor"
test()
