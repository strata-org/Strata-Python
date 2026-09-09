# `-7 // 2`: CPython=-4, Model=-3 — model gives WRONG NUMBER (SMT truncation
# vs Python floor); actively unsound
"""
CPython: -7 // 2 = -4
Model:   from_int(div(-7, 2)) = from_int(-3)  ← DIFFERENT VALUE

The model gives a SPECIFIC WRONG NUMBER, not Hole.
This is the most dangerous divergence: the model is CONFIDENT but WRONG.
"""


def floor_div_examples() -> list[int]:
    results: list[int] = []
    results.append(-7 // 2)   # CPython: -4, Model: -3
    results.append(-1 // 2)   # CPython: -1, Model: 0
    results.append(-5 // 3)   # CPython: -2, Model: -1
    results.append(7 // -2)   # CPython: -4, Model: -3
    results.append(1 // -2)   # CPython: -1, Model: 0
    return results


def main() -> None:
    r: list[int] = floor_div_examples()
    # CPython concrete results:
    assert r[0] == -4   # Model would say -3
    assert r[1] == -1   # Model would say 0
    assert r[2] == -2   # Model would say -1
    assert r[3] == -4   # Model would say -3
    assert r[4] == -1   # Model would say 0

    print(r[0], r[1], r[2], r[3], r[4])


main()
