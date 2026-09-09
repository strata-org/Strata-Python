# A class declares `x: int` at class body level. `__init__` only sets `self.x`
# on one branch (`if flag`). When `flag` is False, `self.x` is never set as an
# instance attribute. Accessing `self.x` raises AttributeError because there's
# no instance attribute and no class-level default value.
"""
a33_conditional_init.py — Field declared but not initialized on all __init__ paths.

mypy trusts the class-level annotation `x: int` and assumes the field exists.
But __init__ only sets self.x on one branch. Accessing self.x on the other
path raises AttributeError.

mypy --strict: Success (0 errors)
Runtime: AttributeError — 'Partial' object has no attribute 'x'
"""


class Partial:
    x: int

    def __init__(self, flag: bool) -> None:
        if flag:
            self.x = 42
        # else: self.x is never set as instance attribute

    def use(self) -> int:
        return self.x + 1  # mypy: int + int. Runtime: AttributeError


def main() -> None:
    p = Partial(False)  # x never set
    p.use()  # AttributeError


if __name__ == "__main__":
    main()
