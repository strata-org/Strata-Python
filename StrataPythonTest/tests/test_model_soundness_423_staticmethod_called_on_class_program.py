# @staticmethod called on class — `MathUtils.add(3,4)` must NOT inject self;
# wrong arity if self added
"""
@staticmethod CALLED ON CLASS — NO SELF/CLS PARAMETER

CPython: class MathUtils:
             @staticmethod
             def add(a: int, b: int) -> int: return a + b
         MathUtils.add(3, 4) → 7

Model:   Finding 125 notes staticmethod must not add implicit first arg.
         If translator adds self/cls: MathUtils_add(???, 3, 4) → wrong arity
         If translator doesn't recognize @staticmethod: may fail entirely.

         The call MathUtils.add(3, 4) must translate to:
         MathUtils_add(3, 4) — NO receiver, NO self, NO cls.

CPython result: 7
Model result: wrong arity error or Hole (if self injected)
"""
from dataclasses import dataclass


class MathUtils:
    @staticmethod
    def add(a: int, b: int) -> int:
        return a + b

    @staticmethod
    def max_of(a: int, b: int) -> int:
        if a >= b:
            return a
        return b

    @staticmethod
    def clamp(x: int, lo: int, hi: int) -> int:
        if x < lo:
            return lo
        if x > hi:
            return hi
        return x


class Validator:
    @staticmethod
    def is_positive(n: int) -> bool:
        return n > 0

    @staticmethod
    def is_in_range(n: int, lo: int, hi: int) -> bool:
        return lo <= n and n <= hi


def main() -> None:
    # Test 1: basic static method call
    assert MathUtils.add(3, 4) == 7
    assert MathUtils.add(0, 0) == 0

    # Test 2: static method with control flow
    assert MathUtils.max_of(5, 3) == 5
    assert MathUtils.max_of(3, 5) == 5

    # Test 3: static method with multiple params
    assert MathUtils.clamp(5, 0, 10) == 5
    assert MathUtils.clamp(-5, 0, 10) == 0
    assert MathUtils.clamp(15, 0, 10) == 10

    # Test 4: static method returning bool
    assert Validator.is_positive(5)
    assert not Validator.is_positive(-3)

    # Test 5: static method with compound condition
    assert Validator.is_in_range(5, 0, 10)
    assert not Validator.is_in_range(15, 0, 10)

    print("all passed")


main()
