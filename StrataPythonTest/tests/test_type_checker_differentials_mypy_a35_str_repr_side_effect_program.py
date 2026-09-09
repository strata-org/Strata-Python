# `__str__` and `__repr__` are allowlisted in the the verifier subset with a
# purity requirement ("return str and have no side effects"). But this purity
# is a semantic predicate — not enforced. If `__str__` mutates a narrowed
# field, `str(obj)` or `f"{obj}"` triggers the mutation without mypy
# invalidating narrowing.
"""
a35_str_repr_side_effect.py — __str__/__repr__ side effect invalidates narrowing.

The Frontend subset allows __str__ and __repr__ but requires them to be pure.
This purity requirement is a SEMANTIC predicate — not enforced syntactically.
If __str__ has a side effect that mutates a narrowed field, mypy doesn't catch it.

str(obj) and f"{obj}" both trigger __str__/__repr__ implicitly.
mypy doesn't consider these as potential narrowing invalidators.

mypy --strict: Success (0 errors)
Runtime: TypeError — str - int
"""


class Logged:
    def __init__(self) -> None:
        self.x: int | str = 42

    def __str__(self) -> str:
        self.x = "logged"
        return "Logged"


def main() -> None:
    obj = Logged()
    if isinstance(obj.x, int):
        msg: str = str(obj)  # calls __str__, mutates obj.x to "logged"
        result: int = obj.x - 1  # mypy: int. Runtime: str - int → TypeError


if __name__ == "__main__":
    main()
