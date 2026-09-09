# Covariant override of mutable field: `Derived.value: int` narrows
# `Base.value: int|str`. Writing str through Base reference breaks Derived.
"""
b1_mutable_override.py — Covariant override of mutable attribute.

No type-changing assignment within a single class. The unsoundness is purely
from subtyping: Derived narrows Base.value from int|str to int, then a function
accepting Base writes str into it.

mypy --strict: Success (0 errors)
mypy --strict --enable-error-code mutable-override: CATCHES IT (but disabled by default)
Runtime: TypeError — str + int fails
"""

class Base:
    value: int | str

    def __init__(self, v: int | str) -> None:
        self.value = v

class Derived(Base):
    value: int  # Covariant override of mutable field — mypy allows by default

    def __init__(self, v: int) -> None:
        self.value = v

    def use_as_int(self) -> int:
        return self.value + 1  # mypy: OK (self.value is int per Derived's annotation)

def set_to_str(b: Base) -> None:
    b.value = "hello"  # mypy: OK (Base.value is int|str, "hello" is str)

def main() -> None:
    d = Derived(42)
    set_to_str(d)  # passes Derived as Base, writes str to .value
    result: int = d.use_as_int()  # mypy: int. Runtime: TypeError
    assert isinstance(result, int), f"TYPE UNSOUND: mypy says int, got {type(result).__name__}"

if __name__ == "__main__":
    main()
