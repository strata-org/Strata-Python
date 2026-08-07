# Augmented `%=` must use the same floored semantics as `%`.
# Regression test: Strata used to compute 1 (Euclidean).
def test() -> None:
    x: int = 7
    x %= -3
    assert x == -2, "augmented modulo with negative divisor"
test()
