# Missing `super().__init__()` exposes class variable (str) where instance
# variable (int) was expected.
"""
b4_missing_super_init.py — Missing super().__init__ exposes class variable with wrong type.

Child declares x: int (covariant override) but never calls super().__init__()
and never sets self.x. Access to self.x falls through to the class variable
on Parent, which has been set to str.

No isinstance narrowing involved. Pure variance + missing initialization.

mypy --strict: Success (0 errors)
Runtime: TypeError — str >> int
"""

class Parent:
    x: int | str

    def __init__(self) -> None:
        self.x = 42

class Child(Parent):
    x: int  # covariant override

    def __init__(self) -> None:
        # Deliberately NOT calling super().__init__()
        # self.x is never set as instance variable
        pass

    def use(self) -> int:
        return self.x >> 1  # mypy: int >> int. Runtime: str >> int → TypeError

def main() -> None:
    Parent.x = "class level"  # set class variable to str
    c = Child()
    c.use()  # self.x falls through to Parent.x = "class level"

if __name__ == "__main__":
    main()
