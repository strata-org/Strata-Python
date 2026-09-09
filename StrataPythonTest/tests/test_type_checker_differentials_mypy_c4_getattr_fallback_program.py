# `__getattr__` returns wrong type after `del self.x` removes instance
# attribute. Access falls to step 4 of the protocol.
"""
c4_getattr_fallback.py — __getattr__ returns wrong type after instance attribute deleted.

No union-typed field changes. The field is declared as int and IS int.
But after `del self.x`, attribute access falls through to __getattr__
which returns str. mypy doesn't model this fallback.

mypy --strict: Success (0 errors)
Runtime: TypeError — str - int
"""

class Fallback:
    def __init__(self) -> None:
        self.x: int = 42

    def __getattr__(self, name: str) -> str:
        return "fallback"

    def clear(self) -> None:
        del self.x  # removes instance attribute; next access hits __getattr__

def main() -> None:
    f = Fallback()
    if isinstance(f.x, int):
        f.clear()
        result: int = f.x - 1  # mypy: int. Runtime: "fallback" - 1 → TypeError

if __name__ == "__main__":
    main()
