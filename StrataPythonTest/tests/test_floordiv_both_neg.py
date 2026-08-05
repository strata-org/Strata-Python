# Both operands negative: (-7) / (-2) is 3.5, floored to 3.
# Regression test: Strata used to compute 4 (Euclidean).
def test() -> None:
    x: int = (-7) // (-2)
    assert x == 3, "floored division with both operands negative"
test()
