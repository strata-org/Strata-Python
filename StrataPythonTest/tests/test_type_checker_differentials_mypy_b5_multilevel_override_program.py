# 3-level inheritance (A→B→C) with covariant field narrowing at each level.
# Writing float through A reference breaks C.
"""
b5_multilevel_override.py — 3-level inheritance with float written through grandparent.

Z3-predicted: if A.field: int|str|float, B.field: int|str, C.field: int,
then writing float through an A reference breaks C's int assumption.

This extends b1 (2-level) to show the exploit works across multiple levels.

mypy --strict: Success (0 errors)
Runtime: TypeError — float >> int (unsupported operand)
"""

class A:
    field: int | str | float
    def __init__(self) -> None:
        self.field = 42
    def set_float(self) -> None:
        self.field = 3.14

class B(A):
    field: int | str  # narrows from A

class C(B):
    field: int  # narrows from B
    def use(self) -> int:
        return self.field >> 1  # int-only operation

def corrupt(a: A) -> None:
    a.set_float()  # writes float, valid for A's type

def main() -> None:
    c = C()
    corrupt(c)  # passes C as A, writes 3.14 (float)
    c.use()     # C.use() does self.field >> 1 → float >> int → TypeError

if __name__ == "__main__":
    main()
