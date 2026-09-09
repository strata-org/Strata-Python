# Mutable default argument accumulates state across calls, eventually
# triggering a type change.
"""
a10_mutable_default.py — Mutable default argument accumulates state across calls.

The mutable default list grows on each call. After enough calls, a threshold
is crossed and the field type changes. mypy doesn't model that default arguments
are shared mutable state.

mypy --strict: Success (0 errors)
Runtime: TypeError — str - int
"""

class Accumulator:
    def __init__(self) -> None:
        self.x: int | str = 0

    def add(self, items: list[int] = []) -> None:  # noqa: B006 — mutable default
        items.append(1)
        if len(items) > 2:
            self.x = "overflow"

def main() -> None:
    a = Accumulator()
    if isinstance(a.x, int):
        a.add()  # default list: [1]
        a.add()  # default list: [1, 1] (SAME list object!)
        a.add()  # default list: [1, 1, 1] → len > 2 → x = "overflow"
        result: int = a.x - 1  # mypy: int. Runtime: str - int → TypeError

if __name__ == "__main__":
    main()
