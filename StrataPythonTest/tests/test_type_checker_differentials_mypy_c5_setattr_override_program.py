# `__setattr__` intercepts assignment and stores wrong type. Field declared as
# int but `__setattr__` stores str.
"""
c5_setattr_override.py — __setattr__ intercepts assignment and stores wrong type.

mypy sees `obj.x = 99` and concludes obj.x is int. But __setattr__ intercepts
the assignment and stores "intercepted" (str) instead. The declared type (int)
and the actual stored value (str) diverge without any union type involved.

This is Category C: no union fields, no inheritance narrowing. The field is
declared as plain `int` but __setattr__ subverts the assignment.

mypy --strict: Success (0 errors)
Runtime: TypeError — str - int
"""

class Interceptor:
    def __init__(self) -> None:
        object.__setattr__(self, "x", 42)
        object.__setattr__(self, "_intercept", False)

    def enable_intercept(self) -> None:
        object.__setattr__(self, "_intercept", True)

    def __setattr__(self, name: str, value: object) -> None:
        if object.__getattribute__(self, "_intercept"):
            object.__setattr__(self, name, "intercepted")  # stores str regardless
        else:
            object.__setattr__(self, name, value)

    x: int  # declared as int

def main() -> None:
    obj = Interceptor()
    obj.enable_intercept()
    obj.x = 99  # mypy: assigns int to int field. Runtime: __setattr__ stores "intercepted"
    result: int = obj.x - 1  # mypy: int - int. Runtime: str - int → TypeError

if __name__ == "__main__":
    main()
