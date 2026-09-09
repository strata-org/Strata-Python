# Boolean short-circuit guards division — `b != 0 and a // b > 5` MUST short-
# circuit; eager eval causes ZeroDivisionError on the guard
"""
Boolean short-circuit `and` used as a GUARD for division:
    if b != 0 and a // b > 5:
        ...

The first conjunct (`b != 0`) guards the second (`a // b`).
If `and` is evaluated eagerly (finding 044), `a // b` executes even
when `b == 0` — causing ZeroDivisionError.

This is the MOST CRITICAL short-circuit pattern: it's the standard
way to prevent division by zero, index out of bounds, and None access.

Uses ONLY Frontend-subset features: int, and, //, if, comparison.
"""


def safe_divide_check(a: int, b: int) -> bool:
    """Guard division with short-circuit and."""
    return b != 0 and a // b > 5


def safe_index_check(xs: list[int], i: int) -> bool:
    """Guard index with bounds check."""
    return i >= 0 and i < len(xs) and xs[i] > 0


def safe_none_check(x: int, flag: bool) -> int:
    """Guard operation with condition."""
    if flag and x > 0:
        return x * 2
    return 0


def chained_guards(a: int, b: int, c: int) -> int:
    """Multiple guards in sequence."""
    if b != 0 and c != 0 and a // b + a // c > 0:
        return a // b + a // c
    return -1


def or_short_circuit(a: int, b: int) -> bool:
    """Or short-circuit: if first is True, don't evaluate second."""
    return b == 0 or a // b < 10


def main() -> None:
    # Safe divide — b != 0 guards the division
    assert safe_divide_check(100, 10) == True   # 10 > 5
    assert safe_divide_check(10, 10) == False   # 1 > 5 is False
    assert safe_divide_check(10, 0) == False    # short-circuits, no ZDE

    # Safe index — bounds check guards access
    assert safe_index_check([1, 2, 3], 1) == True
    assert safe_index_check([1, 2, 3], 5) == False  # out of bounds, no IndexError
    assert safe_index_check([1, -1, 3], 1) == False  # in bounds but negative

    # Chained guards
    assert chained_guards(20, 4, 5) == 9  # 5 + 4
    assert chained_guards(20, 0, 5) == -1  # b==0, short-circuits

    # Or short-circuit
    assert or_short_circuit(10, 0) == True   # b==0 is True, short-circuits
    assert or_short_circuit(5, 2) == True    # 5//2=2 < 10
    assert or_short_circuit(100, 2) == False  # 50 < 10 is False

    print(safe_divide_check(10, 0), safe_index_check([1], 5),
          or_short_circuit(10, 0))


main()
