# Comparison operators >, <=, >= derived from < — derivation must swap/negate
# correctly; wrong derivation swaps < and > or <= and >=
"""
COMPARISON OPERATORS >, <=, >= MAY BE DERIVED FROM < INCORRECTLY

CPython: a > b  ≡ b < a (swap operands, use __lt__)
         a <= b ≡ not (b < a) (negate swapped __lt__)
         a >= b ≡ not (a < b) (negate __lt__)

Model:   The translator may implement >, <=, >= as:
         - Separate PGt, PLe, PGe functions (each needing full dispatch)
         - OR derived from PLt: PGt(a,b) = PLt(b,a), PLe(a,b) = PNot(PLt(b,a))

         If derived, the derivation must be CORRECT:
         - PGt(a, b) = PLt(b, a)  ← operands SWAPPED
         - PLe(a, b) = not PLt(b, a)  ← swap + negate
         - PGe(a, b) = not PLt(a, b)  ← negate only

         If the derivation swaps wrong or negates wrong:
         - PGt(a, b) = PLt(a, b) → WRONG (that's <, not >)
         - PLe(a, b) = not PLt(a, b) → WRONG (that's >=, not <=)

         Each wrong derivation produces WRONG BOOLEAN VALUES.
"""


def test_gt(a: int, b: int) -> bool:
    return a > b


def test_le(a: int, b: int) -> bool:
    return a <= b


def test_ge(a: int, b: int) -> bool:
    return a >= b


def all_comparisons(a: int, b: int) -> list[bool]:
    """All 4 comparisons on same pair — exactly one of <, ==, > is true."""
    return [a < b, a == b, a > b, a <= b, a >= b, a != b]


def float_comparisons(a: float, b: float) -> list[bool]:
    """Same for floats."""
    return [a < b, a == b, a > b, a <= b, a >= b]


def main() -> None:
    # Test 1: > is the reverse of <
    assert test_gt(5, 3)
    assert not test_gt(3, 5)
    assert not test_gt(3, 3)

    # Test 2: <= includes equality
    assert test_le(3, 5)
    assert test_le(3, 3)
    assert not test_le(5, 3)

    # Test 3: >= includes equality
    assert test_ge(5, 3)
    assert test_ge(3, 3)
    assert not test_ge(3, 5)

    # Test 4: consistency check — all comparisons on (5, 3)
    r: list[bool] = all_comparisons(5, 3)
    # 5 < 3 = False, 5 == 3 = False, 5 > 3 = True
    # 5 <= 3 = False, 5 >= 3 = True, 5 != 3 = True
    assert r == [False, False, True, False, True, True]

    # Test 5: all comparisons on (3, 3)
    r2: list[bool] = all_comparisons(3, 3)
    # 3 < 3 = False, 3 == 3 = True, 3 > 3 = False
    # 3 <= 3 = True, 3 >= 3 = True, 3 != 3 = False
    assert r2 == [False, True, False, True, True, False]

    # Test 6: float comparisons
    rf: list[bool] = float_comparisons(1.5, 2.5)
    assert rf == [True, False, False, True, False]

    print("all passed")


main()
