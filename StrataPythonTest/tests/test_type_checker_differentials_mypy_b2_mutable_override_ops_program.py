# Same as b1 but demonstrating various int-only operators (unary -, hex(),
# list[], >>) that produce TypeError.
"""
b2_mutable_override_ops.py — Covariant mutable override + various int-only operations.

Same mechanism as b1 (covariant override of mutable field, write through base class)
but demonstrating that ANY int-only operation becomes a TypeError vector.

mypy --strict: Success (0 errors)
Runtime: TypeError on all operations
"""

class Base:
    val: int | str
    def __init__(self, v: int | str) -> None:
        self.val = v

class IntSub(Base):
    val: int  # covariant override — mypy allows by default
    def __init__(self, v: int) -> None:
        self.val = v

    def negate(self) -> int:
        return -self.val

    def to_hex(self) -> str:
        return hex(self.val)

    def index_into(self, lst: list[str]) -> str:
        return lst[self.val]

    def right_shift(self) -> int:
        return self.val >> 1

    def modulo(self) -> int:
        return self.val % 7

def corrupt(b: Base) -> None:
    b.val = "not an int"

def main() -> None:
    s = IntSub(1)
    corrupt(s)
    try:
        s.negate()
    except TypeError as e:
        print(f"  TypeError via unary -: {e}")

    s = IntSub(1)
    corrupt(s)
    try:
        s.to_hex()
    except TypeError as e:
        print(f"  TypeError via hex(): {e}")

    s = IntSub(1)
    corrupt(s)
    try:
        s.index_into(["a", "b", "c"])
    except TypeError as e:
        print(f"  TypeError via list[]: {e}")

    s = IntSub(1)
    corrupt(s)
    try:
        s.right_shift()
    except TypeError as e:
        print(f"  TypeError via >>: {e}")

if __name__ == "__main__":
    main()
