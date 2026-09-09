# `-7 % 3`: CPython=2, Model=-1 — model gives WRONG SIGN (SMT mod vs Python
# mod); actively unsound
"""
CPython: -7 % 3 = 2
Model:   from_int(mod(-7, 3)) = from_int(-1)  ← WRONG SIGN

The model gives a number with the WRONG SIGN.
Python % result has same sign as divisor. SMT mod has same sign as dividend.
"""


def modulo_examples() -> list[int]:
    results: list[int] = []
    results.append(-7 % 3)    # CPython: 2,  Model: -1
    results.append(-1 % 3)    # CPython: 2,  Model: -1
    results.append(7 % -3)    # CPython: -2, Model: 1
    results.append(1 % -3)    # CPython: -2, Model: 1
    results.append(-10 % 4)   # CPython: 2,  Model: -2
    return results


def is_even(n: int) -> bool:
    """n % 2 == 0 — works for positive n, but what about negative?"""
    return n % 2 == 0


def main() -> None:
    r: list[int] = modulo_examples()
    # CPython concrete results:
    assert r[0] == 2    # Model would say -1
    assert r[1] == 2    # Model would say -1
    assert r[2] == -2   # Model would say 1
    assert r[3] == -2   # Model would say 1
    assert r[4] == 2    # Model would say -2

    # is_even works for positive (both agree)
    assert is_even(4) == True
    assert is_even(3) == False
    # is_even for negative: CPython -4%2=0 (even), -3%2=1 (odd? NO: -3%2=1 not 0)
    # Actually: -3 % 2 = 1 in CPython (sign of divisor=positive)
    # SMT: -3 mod 2 = -1 (sign of dividend=negative)
    # CPython: -3 % 2 == 0? No, it's 1. So is_even(-3) = (1==0) = False ✓
    # Model: -3 mod 2 = -1. is_even(-3) = (-1==0) = False ✓ (accidentally same!)
    # But: -4 % 2: CPython = 0, SMT mod = 0. Both agree for even numbers.
    assert is_even(-4) == True
    assert is_even(-3) == False

    print(r[0], r[1], r[2], r[3], r[4])


main()
