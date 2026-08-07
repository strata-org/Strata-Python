# bool operands promote to int: True // (-3) == 1 // (-3) == -1 (floor of -0.333).
# Regression test: Strata used to compute 0 (Euclidean).
def test() -> None:
    x: int = True // (-3)
    assert x == -1, "bool floored division with negative divisor"
test()
