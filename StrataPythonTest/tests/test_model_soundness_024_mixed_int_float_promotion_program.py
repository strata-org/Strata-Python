# Mixed int/float arithmetic (`3 + 1.5`) — `PAdd` only handles same-type
# pairs; cross-type `from_int × from_float` falls to Hole
"""
Python promotes int to float in mixed arithmetic: int + float -> float.
The Laurel PAdd/PSub/PMul likely only handle from_int × from_int and
from_float × from_float, but not the cross-type from_int × from_float case.
"""


def scale(value: int, factor: float) -> float:
    # int * float -> float in Python
    return value * factor


def offset(base: float, delta: int) -> float:
    # float + int -> float in Python
    return base + delta


def average(total: int, count: int) -> float:
    # int / int -> float (true division), but also:
    # int + float -> float for accumulation patterns
    result: float = 0.0
    result = result + total  # float + int -> float
    return result / count


def main() -> None:
    # int * float -> float
    a: float = scale(3, 2.5)
    assert a == 7.5

    # float + int -> float
    b: float = offset(1.5, 2)
    assert b == 3.5

    # float - int -> float
    c: float = 10.0 - 3
    assert c == 7.0

    # int + float -> float
    d: float = 3 + 1.5
    assert d == 4.5

    # int ** float -> float (even when result is exact)
    # Actually ** with float exponent is OUT, but int * float is IN

    print(a, b, c, d)


main()
