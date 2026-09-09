# Builder pattern (`return self`) — creates alias between original and return
# value; value semantics loses the link
"""
A method that modifies `self` and returns `self` (builder/fluent pattern)
creates an aliasing situation: the caller's original reference and the
return value point to the SAME object in CPython. Under value semantics,
the return value is a modified COPY — the original is unchanged.

This diverges when the caller checks the original variable after calling
the method through a chain or via a separate variable.
"""
from dataclasses import dataclass


@dataclass
class Builder:
    parts: list[str]
    count: int

    def add(self: "Builder", part: str) -> "Builder":
        self.parts = self.parts + [part]
        self.count = self.count + 1
        return self  # returns self AFTER mutation


def chained_build(parts: list[str]) -> Builder:
    b: Builder = Builder(parts=[], count=0)
    for p in parts:
        b = b.add(p)  # reassign b each time
    return b


def divergence_demo() -> int:
    """Shows where value semantics diverges from CPython."""
    original: Builder = Builder(parts=[], count=0)
    modified: Builder = original.add("hello")
    # CPython: original IS modified (same object, mutated)
    #   original.count == 1, modified.count == 1
    # Model: original is UNCHANGED, modified is a new value
    #   original.count == 0, modified.count == 1
    return original.count  # CPython: 1, Model: 0


def main() -> None:
    # Chained build with reassignment: works in both
    result: Builder = chained_build(["a", "b", "c"])
    assert result.parts == ["a", "b", "c"]
    assert result.count == 3

    # The divergence: original vs modified
    orig_count: int = divergence_demo()
    # CPython: returns 1 (original was mutated via self)
    assert orig_count == 1

    print(result.count, orig_count)


main()
