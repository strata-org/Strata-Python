# Subtraction cross-type dispatch — `int - float`, `float - int`, `bool - int`
# fall to Hole (same gap as finding 024)
"""
Subtraction (`-`) has the same cross-type dispatch gaps as addition:
- int - float → float (promotion)
- float - int → float (promotion)
- bool - int → int (bool promotes to int)
- int - bool → int (bool promotes to int)

If PSub only handles same-type pairs (int-int, float-float), cross-type
subtraction falls to Hole. This is the subtraction analog of finding 024.
"""


def int_minus_float(a: int, b: float) -> float:
    return a - b


def float_minus_int(a: float, b: int) -> float:
    return a - b


def bool_minus_int(a: bool, b: int) -> int:
    return a - b


def distance(x1: int, y1: int, x2: float, y2: float) -> float:
    dx: float = x1 - x2  # int - float → float
    dy: float = y1 - y2  # int - float → float
    return dx * dx + dy * dy


def countdown(start: int, step: float) -> float:
    return start - step  # int - float → float


def main() -> None:
    # int - float
    assert int_minus_float(5, 2.5) == 2.5
    assert int_minus_float(10, 3.0) == 7.0

    # float - int
    assert float_minus_int(5.5, 2) == 3.5
    assert float_minus_int(10.0, 3) == 7.0

    # bool - int (True=1, False=0)
    assert bool_minus_int(True, 1) == 0
    assert bool_minus_int(False, 1) == -1

    # Mixed in expression
    assert distance(0, 0, 3.0, 4.0) == 25.0  # 9 + 16

    # Countdown
    assert countdown(10, 2.5) == 7.5

    print(int_minus_float(5, 2.5), float_minus_int(5.5, 2), bool_minus_int(True, 1))


main()
