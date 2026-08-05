# Python uses floored division: the quotient rounds toward negative infinity.
# Regression test for the Euclidean-division soundness bug (Strata used to
# compute -3 here). See Python Language Reference 6.7.
def test() -> None:
    x: int = 7 // (-2)
    assert x == -4, "floored division with negative divisor"
test()
