# Incorrect `//` negative: CPython `-7//2=-4`, Model `-3` — SMT div truncates
# toward 0 instead of floor toward -∞
"""
INCORRECT OPERATOR BEHAVIOR: // on negative operands.

CPython: -7 // 2 = -4 (floor toward -∞)
Model:   -7 // 2 = -3 (SMT div truncates toward 0)

The model computes a SPECIFIC WRONG NUMBER. Not Hole — a concrete
incorrect value that the solver uses as fact.
"""


def test_floor_div() -> list[int]:
    results: list[int] = []
    results.append(-7 // 2)    # CPython: -4, Model: -3
    results.append(-1 // 2)    # CPython: -1, Model: 0
    results.append(7 // -2)    # CPython: -4, Model: -3
    results.append(-10 // 3)   # CPython: -4, Model: -3
    results.append(1 // -3)    # CPython: -1, Model: 0
    return results


def main() -> None:
    r: list[int] = test_floor_div()
    assert r == [-4, -1, -4, -4, -1]
    print(r)


main()
