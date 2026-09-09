# Two wrapper objects (`ViewA`, `ViewB`) hold references to the same `Shared`
# instance. isinstance narrows `a.shared.x` to int. Calling `b.shared.clear()`
# mutates the shared object's `x` field through a completely different access
# path. Mypy doesn't track that `a.shared` and `b.shared` are the same object.
"""
a23_shared_composition.py — Mutation through shared composition invalidates narrowing.

Two objects (ViewA, ViewB) hold references to the same Shared instance.
isinstance narrows a.shared.x to int. Calling b.shared.clear() mutates
the shared object's x field. a.shared.x is now str.

mypy --strict: Success (0 errors)
Runtime: TypeError — str - int
"""


class Shared:
    def __init__(self) -> None:
        self.x: int | str = 42

    def clear(self) -> None:
        self.x = "cleared"


class ViewA:
    def __init__(self, s: Shared) -> None:
        self.shared: Shared = s


class ViewB:
    def __init__(self, s: Shared) -> None:
        self.shared: Shared = s


def main() -> None:
    s = Shared()
    a = ViewA(s)
    b = ViewB(s)
    if isinstance(a.shared.x, int):
        b.shared.clear()  # mutates s.x via b's reference
        # mypy: a.shared.x is int (narrowed). Runtime: "cleared" (str)
        result: int = a.shared.x - 1  # TypeError


if __name__ == "__main__":
    main()
