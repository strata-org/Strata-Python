# True division `/` has no `PTrueDiv`; `int / int` must return `float` but
# likely returns `int` or Hole
"""
Python's `/` operator (true division) ALWAYS returns a float, even when
both operands are int and the result is exact: 10 / 2 == 5.0 (float).
The Laurel encoding has no dedicated PTrueDiv — it likely maps `/` to
PFloorDiv (returning int) or to a Hole.
"""


def half(n: int) -> float:
    return n / 2


def ratio(a: int, b: int) -> float:
    if b == 0:
        raise ValueError("division by zero")
    return a / b


def main() -> None:
    # 10 / 2 returns 5.0 (float), NOT 5 (int)
    x: float = half(10)
    assert x == 5.0

    # 7 / 2 returns 3.5
    y: float = ratio(7, 2)
    assert y == 3.5

    # 1 / 3 returns 0.333...
    z: float = ratio(1, 3)
    assert z < 0.34
    assert z > 0.33

    # Even exact division returns float
    w: float = ratio(6, 3)
    assert w == 2.0

    print(x, y, z, w)


main()
