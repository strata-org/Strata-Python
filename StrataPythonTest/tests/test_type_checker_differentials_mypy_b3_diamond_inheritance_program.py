# Diamond inheritance: class D(B, C) inherits B's narrow field AND C's
# mutating method.
"""
b3_diamond_inheritance.py — Diamond inheritance combines narrow field with mutating method.

Class B narrows x: int|str to x: int. Class C has set_str() that writes str.
Class D inherits both. D.use_x() assumes int, D.set_str() writes str.
No explicit override needed — the conflict comes from the diamond.

mypy --strict: Success (0 errors)
Runtime: TypeError — str >> int
"""

class A:
    x: int | str
    def __init__(self) -> None:
        self.x = 42

class B(A):
    x: int  # covariant override (narrows)
    def use_x(self) -> int:
        return self.x >> 1  # assumes int

class C(A):
    def set_str(self) -> None:
        self.x = "hello"  # writes str (legal per A's type)

class D(B, C):  # inherits B's narrow x:int AND C's set_str
    pass

def main() -> None:
    d = D()
    d.set_str()  # from C: sets x to "hello"
    d.use_x()   # from B: does "hello" >> 1 → TypeError

if __name__ == "__main__":
    main()
