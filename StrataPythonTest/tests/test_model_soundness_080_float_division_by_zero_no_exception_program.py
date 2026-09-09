# Float division by zero — SMT `Real` division is total; model allows `1.0 /
# 0.0` without raising ZeroDivisionError
"""
In CPython, `1.0 / 0.0` raises ZeroDivisionError. But the model uses
SMT-LIB `Real` for from_float, and real-valued division by zero is
either undefined or produces an unconstrained value in SMT (not an
exception). The model may allow `x / 0.0` to succeed silently,
returning an arbitrary real number instead of raising.

Similarly, `1 / 0` (true division) and `1 // 0` (floor division)
should raise ZeroDivisionError, but the model's precondition may
only be checked for int division, not float division.
"""


def safe_ratio(a: float, b: float) -> float:
    if b == 0.0:
        return 0.0
    return a / b


def inverse(x: float) -> float:
    return 1.0 / x


def normalize(values: list[float], total: float) -> list[float]:
    result: list[float] = []
    for v in values:
        result = result + [v / total]
    return result


def main() -> None:
    # Normal float division
    assert safe_ratio(10.0, 2.0) == 5.0
    assert safe_ratio(10.0, 0.0) == 0.0  # guarded

    # Float division by zero raises
    raised: bool = False
    try:
        x: float = 1.0 / 0.0
    except ZeroDivisionError:
        raised = True
    assert raised == True

    # Int true division by zero also raises
    raised2: bool = False
    try:
        y: float = 1 / 0
    except ZeroDivisionError:
        raised2 = True
    assert raised2 == True

    # Inverse of zero raises
    raised3: bool = False
    try:
        z: float = inverse(0.0)
    except ZeroDivisionError:
        raised3 = True
    assert raised3 == True

    # Normal normalize
    normed: list[float] = normalize([2.0, 3.0, 5.0], 10.0)
    assert normed[0] == 0.2
    assert normed[1] == 0.3

    print(safe_ratio(10.0, 2.0), raised, raised2)


main()
