# isinstance narrowing on `obj.data: int|str` not invalidated when an external
# function mutates through an alias `ref = obj`.
"""
a2_narrowing_alias.py — isinstance narrowing invalidated by mutation through alias.

mypy --strict: Success (0 errors)
Runtime: AssertionError — variable is str where mypy says int
"""

class Holder:
    def __init__(self) -> None:
        self.data: int | str = 10

def mutate_holder(h: Holder) -> None:
    h.data = "now a string"

def main() -> None:
    obj = Holder()
    ref: Holder = obj  # alias — same object
    if isinstance(obj.data, int):
        mutate_holder(ref)  # mutates obj.data through the alias
        val: int = obj.data - 1  # mypy: int - int. Runtime: str - int → TypeError

if __name__ == "__main__":
    main()
