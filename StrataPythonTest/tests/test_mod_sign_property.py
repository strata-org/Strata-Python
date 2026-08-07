# The remainder is negative when the divisor is negative.
# Regression test: Strata used to compute 1 (Euclidean, always non-negative).
def test() -> None:
    x: int = 10 % (-3)
    assert x == -2, "modulo result sign follows divisor sign"
test()
