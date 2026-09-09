# Incorrect `/` returns int: CPython `7/2=3.5` (float), Model `3` (int) or
# Hole — true div ALWAYS returns float
"""
INCORRECT OPERATOR BEHAVIOR: / on int operands returns wrong TYPE.

CPython: 7 / 2 = 3.5 (ALWAYS float, even for int/int)
Model:   7 / 2 = 3 (if mapped to floor div) or Hole (if no PTrueDiv)

The RETURN TYPE is wrong: should be from_float, model gives from_int.
"""


def true_div_examples() -> list[float]:
    results: list[float] = []
    results.append(7 / 2)     # CPython: 3.5 (float)
    results.append(6 / 3)     # CPython: 2.0 (float! not int 2)
    results.append(1 / 4)     # CPython: 0.25 (float)
    results.append(-7 / 2)    # CPython: -3.5 (float)
    results.append(0 / 1)     # CPython: 0.0 (float! not int 0)
    return results


def type_is_always_float() -> bool:
    """Even exact division returns float."""
    x: float = 6 / 3  # 2.0, not 2
    return x == 2.0


def main() -> None:
    r: list[float] = true_div_examples()
    assert r[0] == 3.5
    assert r[1] == 2.0   # float, not int!
    assert r[2] == 0.25
    assert r[3] == -3.5
    assert r[4] == 0.0   # float, not int!

    assert type_is_always_float() == True

    print(r[0], r[1], r[4])


main()
