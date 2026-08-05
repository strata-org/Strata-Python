# Augmented `//=` must use the same floored semantics as `//`.
# Regression test: Strata used to compute -3 (Euclidean).
def test() -> None:
    x: int = 7
    x //= -2
    assert x == -4, "augmented floored division with negative divisor"
test()
