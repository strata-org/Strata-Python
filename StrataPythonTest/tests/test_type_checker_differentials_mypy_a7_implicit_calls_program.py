# `__contains__` (via `in`), `__format__` (via f-string), comprehension filter
# side effects invalidate narrowing.
"""
a7_implicit_calls.py — More implicit dunder calls that invalidate narrowing.

Extends a5 with additional Python syntax that triggers hidden method calls:
- `x in obj` → __contains__
- `f"{obj}"` → __format__
- `[... if obj.method() ...]` → filter in comprehension

mypy --strict: Success (0 errors)
Runtime: TypeError on all three
"""

# --- __contains__ via 'in' operator ---
class ContainsMutates:
    def __init__(self) -> None:
        self.x: int | str = 10
        self.items: set[int] = {1, 2, 3}

    def __contains__(self, item: object) -> bool:
        self.x = "mutated"
        return item in self.items

def test_contains() -> None:
    s = ContainsMutates()
    if isinstance(s.x, int):
        _ = (1 in s)  # calls __contains__, mutates s.x
        result: int = s.x - 1  # TypeError

# --- __format__ via f-string ---
class FormatMutates:
    def __init__(self) -> None:
        self.x: int | str = 10

    def __format__(self, spec: str) -> str:
        self.x = "formatted"
        return "result"

def test_format() -> None:
    f = FormatMutates()
    if isinstance(f.x, int):
        _ = f"{f}"  # calls __format__, mutates f.x
        result: int = f.x - 1  # TypeError

# --- Comprehension filter with side effect ---
class FilterMutates:
    def __init__(self) -> None:
        self.x: int | str = 10

    def check(self, item: int) -> bool:
        if item > 1:
            self.x = "corrupted"
        return item > 0

def test_filter() -> None:
    s = FilterMutates()
    if isinstance(s.x, int):
        _ = [i for i in [1, 2, 3] if s.check(i)]  # filter mutates s.x
        result: int = s.x - 1  # TypeError

def main() -> None:
    tests = [
        ("'in' (__contains__)", test_contains),
        ("f-string (__format__)", test_format),
        ("comprehension filter", test_filter),
    ]
    for name, fn in tests:
        try:
            fn()
        except TypeError as e:
            print(f"  TypeError via {name}: {e}")

if __name__ == "__main__":
    main()
