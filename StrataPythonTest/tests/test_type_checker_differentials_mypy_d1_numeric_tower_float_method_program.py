# PEP 484 numeric tower declares `int <: float`. Mypy allows passing `int`
# where `float` is expected. But `float` has methods (`hex()`, `fromhex()`)
# that `int` doesn't. Calling these on the actual `int` value produces
# AttributeError.
"""
d1_numeric_tower_float_method.py — Numeric tower: int passed where float expected, float-only method called.

PEP 484 numeric tower: int <: float. So mypy allows passing int where float is expected.
But float has methods that int doesn't (e.g., .hex()). Calling such a method
on the actual int value produces AttributeError.

mypy --strict: Success (0 errors)
Runtime: AttributeError — 'int' object has no attribute 'hex'

NOTE: This produces AttributeError, not TypeError. Still a type-safety violation.
The Frontend subset says "Integer/float conversions at call boundaries" is OUT,
which would block this. Documented for completeness.
"""


def float_to_hex(x: float) -> str:
    return x.hex()


def main() -> None:
    result: str = float_to_hex(1)  # int passed where float expected


if __name__ == "__main__":
    main()
