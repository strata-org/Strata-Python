# Keyword args reordered — `divide(b=3, a=10)` must map by name to position;
# call-site order gives `3//10=0` instead of `10//3=3`
"""
KEYWORD ARGUMENTS REORDERED AT CALL SITE

CPython: def divide(a: int, b: int) -> int: return a // b
         divide(b=3, a=10) → 3 (a=10, b=3, computes 10//3)

Model:   If translator uses CALL-SITE ORDER instead of PARAMETER ORDER:
         divide(b=3, a=10) → divide(3, 10) → 3 // 10 = 0 (WRONG!)

         The translator must map keyword arguments BY NAME to their
         POSITIONAL slot in the function signature, regardless of
         the order they appear at the call site.

CPython result: divide(b=3, a=10) == 3
Model result (if order-based): 0 (computes 3 // 10)
"""


def divide(a: int, b: int) -> int:
    return a // b


def power(base: int, exp: int) -> int:
    result: int = 1
    i: int = 0
    while i < exp:
        result *= base
        i += 1
    return result


def make_range(start: int, stop: int, step: int) -> list[int]:
    result: list[int] = []
    i: int = start
    while i < stop:
        result.append(i)
        i += step
    return result


def main() -> None:
    # Test 1: keyword args in reverse order
    assert divide(b=3, a=10) == 3  # 10 // 3 = 3
    # If model uses call-site order: divide(3, 10) = 3 // 10 = 0 (WRONG)

    # Test 2: positional order (baseline)
    assert divide(10, 3) == 3

    # Test 3: another non-commutative function
    assert power(base=2, exp=3) == 8
    assert power(exp=3, base=2) == 8  # same result regardless of kwarg order

    # Test 4: three keyword args reordered
    r: list[int] = make_range(step=2, stop=10, start=0)
    assert r == [0, 2, 4, 6, 8]

    # Test 5: mix of positional and keyword
    assert divide(10, b=3) == 3

    print("all passed")


main()
