# `__getattribute__` override returns wrong type based on internal state.
# Field declared as int but override returns str.
"""
c6_getattribute_override.py — __getattribute__ returns wrong type based on internal state.

mypy trusts the declared field type (x: int). But __getattribute__ intercepts
ALL attribute access and can return anything. After calling corrupt(), the
override returns str instead of int.

No narrowing involved. No union types on the field. The field is declared as
plain `int` but __getattribute__ subverts the access.

mypy --strict: Success (0 errors)
Runtime: TypeError — str - int
"""

class Intercepted:
    def __init__(self) -> None:
        object.__setattr__(self, "_x", 42)
        object.__setattr__(self, "_corrupted", False)

    x: int  # declared type

    def __getattribute__(self, name: str) -> object:
        if name == "x":
            if object.__getattribute__(self, "_corrupted"):
                return "not int"
            return object.__getattribute__(self, "_x")
        return object.__getattribute__(self, name)

    def corrupt(self) -> None:
        object.__setattr__(self, "_corrupted", True)

def main() -> None:
    obj = Intercepted()
    obj.corrupt()
    val: int = obj.x  # mypy: int (from annotation). Runtime: "not int" (str)
    result: int = val - 1  # TypeError

if __name__ == "__main__":
    main()
