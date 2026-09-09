# isinstance on tuple element (`h.pair[0]`) narrowed, then `h.to_strs()`
# replaces the entire tuple.
"""
a16_tuple_element_narrowing.py — Narrowing on tuple element invalidated by mutation.

isinstance(h.pair[0], int) narrows the element type. Then h.to_strs() replaces
the entire tuple with string values. The narrowing on the element persists.

mypy --strict: Success (0 errors)
Runtime: TypeError — str - int
"""

class Holder:
    def __init__(self) -> None:
        self.pair: tuple[int, int] | tuple[str, str] = (1, 2)

    def to_strs(self) -> None:
        self.pair = ("a", "b")

def main() -> None:
    h = Holder()
    if isinstance(h.pair[0], int):
        h.to_strs()  # replaces pair with ("a", "b")
        first: int = h.pair[0]  # mypy: int (narrowed). Runtime: "a" (str)
        result: int = first - 1  # TypeError

if __name__ == "__main__":
    main()
