# Implicit dunder calls (`__eq__`, `__bool__`, `__len__`, `__iter__`) mutate
# fields. Triggered by `==`, `if obj`, `len()`, `for`.
"""
a5_dunder_side_effects.py — Dunder methods with side effects invalidate narrowing.

mypy does not consider that __eq__, __bool__, __len__, __iter__ can mutate fields.
These are called IMPLICITLY by Python syntax (==, if, len(), for) so the mutation
is invisible at the source level.

mypy --strict: Success (0 errors)
Runtime: TypeError on all four sub-examples
"""

# --- __eq__ mutates on comparison ---
class EqMutates:
    def __init__(self, val: int | str) -> None:
        self.val: int | str = val
    def __eq__(self, other: object) -> bool:
        self.val = "mutated"
        return True

def test_eq() -> None:
    e = EqMutates(42)
    if isinstance(e.val, int):
        _ = (e == 0)  # calls __eq__, mutates e.val to str
        result: int = e.val - 1  # mypy: int - int. Runtime: str - int → TypeError

# --- __bool__ mutates on truthiness test ---
class BoolMutates:
    def __init__(self) -> None:
        self.x: int | str = 10
    def __bool__(self) -> bool:
        self.x = "now str"
        return True

def test_bool() -> None:
    b = BoolMutates()
    if isinstance(b.x, int):
        if b:  # calls __bool__, mutates b.x
            result: int = b.x - 1  # TypeError

# --- __len__ mutates on len() call ---
class LenMutates:
    def __init__(self) -> None:
        self.x: int | str = 10
        self.items: list[int] = [1, 2, 3]
    def __len__(self) -> int:
        self.x = "corrupted"
        return len(self.items)

def test_len() -> None:
    obj = LenMutates()
    if isinstance(obj.x, int):
        n: int = len(obj)  # calls __len__, mutates obj.x
        result: int = obj.x + n  # TypeError

# --- __iter__ mutates on for-loop entry ---
class IterMutates:
    def __init__(self) -> None:
        self.x: int | str = 10
        self.data: list[int] = [1, 2]
    def __iter__(self) -> "IterMutates":
        self.x = "gone"
        return self
    def __next__(self) -> int:
        if self.data:
            return self.data.pop()
        raise StopIteration

def test_iter() -> None:
    s = IterMutates()
    if isinstance(s.x, int):
        for item in s:  # calls __iter__, mutates s.x
            pass
        result: int = s.x - 1  # TypeError

def main() -> None:
    tests = [
        ("__eq__ side effect", test_eq),
        ("__bool__ side effect", test_bool),
        ("__len__ side effect", test_len),
        ("__iter__ side effect", test_iter),
    ]
    for name, fn in tests:
        try:
            fn()
        except TypeError as e:
            print(f"  TypeError via {name}: {e}")

if __name__ == "__main__":
    main()
