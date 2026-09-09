# with-statement `__enter__` mutates a field that was narrowed before the with
# block.
"""
a8_context_manager.py — with-statement __enter__ mutates narrowed field.

The 'with' statement calls __enter__ which is an implicit method call that
mypy doesn't consider as a narrowing invalidator.

mypy --strict: Success (0 errors)
Runtime: TypeError — str - int
"""

class MutatingCtx:
    def __init__(self, target: "Victim") -> None:
        self.target = target

    def __enter__(self) -> str:
        self.target.x = "entered"
        return "ctx"

    def __exit__(self, *args: object) -> None:
        pass

class Victim:
    def __init__(self) -> None:
        self.x: int | str = 42

def main() -> None:
    v = Victim()
    if isinstance(v.x, int):
        with MutatingCtx(v) as ctx:
            result: int = v.x - 1  # mypy: int. Runtime: TypeError

if __name__ == "__main__":
    main()
