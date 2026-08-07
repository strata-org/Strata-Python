# Both operands negative: remainder follows the divisor's sign.
# Regression test: Strata used to compute 1 (Euclidean).
def test() -> None:
    x: int = (-7) % (-2)
    assert x == -1, "modulo with both operands negative"
test()
