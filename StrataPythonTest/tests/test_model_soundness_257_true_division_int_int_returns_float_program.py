# `int / int` returns float — true division ALWAYS returns float; model may
# use floor div (wrong value) or have no PTrueDiv (Hole)
"""
CPython: 7 / 2 → 3.5 (float, true division)
Model:   PTrueDiv(from_int(7), from_int(2)) → from_int(3) or Hole

True division ALWAYS returns float in Python 3, even for int operands.
If the model uses integer division or has no PTrueDiv, the result is wrong.
"""


def true_div(a: int, b: int) -> float:
    return a / b


def main() -> None:
    # CPython: 7 / 2 = 3.5 (float, NOT 3)
    assert true_div(7, 2) == 3.5
    # Model: if using PFloorDiv → from_int(3). WRONG type AND value.
    # Model: if PTrueDiv missing → Hole. WRONG.

    assert true_div(10, 4) == 2.5
    assert true_div(1, 3) == 0.3333333333333333
    assert true_div(6, 3) == 2.0  # even exact division returns float
    assert true_div(-7, 2) == -3.5

    print(true_div(7, 2), true_div(6, 3), true_div(-7, 2))


main()
