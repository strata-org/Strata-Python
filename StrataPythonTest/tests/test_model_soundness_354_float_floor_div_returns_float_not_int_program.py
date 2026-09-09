# Float `//` returns `from_float` not `from_int` — `7.0 // 2.0 = 3.0` (float);
# model may return wrong tag or Hole
"""
FLOAT FLOOR DIVISION RETURNS FLOAT NOT INT

CPython: 7.0 // 2.0 → 3.0 (float!)
         7.0 // 2   → 3.0 (float!)
         7 // 2     → 3   (int)

         The return TYPE of // depends on operand types:
         int // int → int
         float // float → float
         float // int → float
         int // float → float

Model:   PFloorDiv likely only handles (from_int, from_int) → from_int.
         (from_float, from_float) either:
         - Has no case → Hole
         - Returns from_int (WRONG TYPE — should be from_float)
         - Returns from_float but with wrong value (SMT div semantics)

Finding 050 mentions this issue exists. This finding provides the
concrete program and demonstrates the TYPE TAG divergence specifically.
"""


def float_floor_div(a: float, b: float) -> float:
    """float // float → float (not int!)."""
    return a // b


def mixed_floor_div(a: int, b: float) -> float:
    """int // float → float."""
    return a // b


def divide_evenly(total: float, parts: float) -> float:
    """Practical use: how many whole units fit."""
    return total // parts


def main() -> None:
    # Test 1: float // float returns FLOAT
    result: float = float_floor_div(7.0, 2.0)
    # CPython: 3.0 (type: float)
    # Model: Hole (no float case) or from_int(3) (wrong tag)
    assert result == 3.0
    assert isinstance(result, float)  # NOT int!

    # Test 2: negative float floor div
    result2: float = float_floor_div(-7.0, 2.0)
    # CPython: -4.0 (floors toward -∞, returns float)
    assert result2 == -4.0

    # Test 3: int // float → float
    result3: float = mixed_floor_div(7, 2.0)
    assert result3 == 3.0
    assert isinstance(result3, float)

    # Test 4: result is float even when "looks like int"
    result4: float = float_floor_div(6.0, 2.0)
    assert result4 == 3.0
    assert isinstance(result4, float)  # Still float!

    # Test 5: practical use
    assert divide_evenly(10.5, 3.0) == 3.0
    assert divide_evenly(100.0, 7.0) == 14.0

    print("all passed")


main()
