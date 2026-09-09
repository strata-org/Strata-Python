# `'x' in d` narrowing invalidated by `del d['x']` through a method call.
# Produces KeyError, not TypeError.
"""
c1_dict_in_narrowing.py — 'in' narrowing invalidated by deletion through method call.

No union types. No type-changing assignments. No inheritance.
Just a dict, an 'in' check, and a method that deletes the key.

mypy --strict: Success (0 errors)
Runtime: KeyError
"""

class Config:
    def __init__(self) -> None:
        self.data: dict[str, int] = {"x": 1}

    def clear_x(self) -> None:
        del self.data["x"]

def main() -> None:
    c = Config()
    if "x" in c.data:
        c.clear_x()  # deletes the key we just checked for
        val: int = c.data["x"]  # mypy: OK ('in' narrowing). Runtime: KeyError
        assert isinstance(val, int)

if __name__ == "__main__":
    main()
