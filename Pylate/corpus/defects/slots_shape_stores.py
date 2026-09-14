"""Storing outside the declared layout, at both strengths.

The distinction is the whole point of admitting `__slots__`. Where the receiver's
class is slots-complete over its MRO, CPython has nowhere to put the field, so the
store *always* raises and the analyzer reports a `guaranteed-error` with no normal
edge. Where the class has a `__dict__`, CPython permits the store, so the raise is
only possible: the analyzer keeps both edges and files `attr-missing`.

Both are reported, which is what matters. mypy, ty and pyright all reject the
plain case too, so treating it as an error rather than a silent success is the
mainstream reading, not a strict one.

`Holder` exists so the field name is declared *somewhere*; a name no class
declares is refused earlier by `shape-store`.
"""


class Holder:
    def __init__(self) -> None:
        self.extra: int = 0


class Slotted:
    __slots__ = ("n",)

    def __init__(self) -> None:
        self.n: int = 0


class Plain:
    def __init__(self) -> None:
        self.n: int = 0


class LeakySub(Slotted):
    """Declares no `__slots__`, so instances get a `__dict__` back."""


def guaranteed_error() -> int:
    s = Slotted()
    s.extra = 5
    return s.n


def maybe_error_plain() -> int:
    p = Plain()
    p.extra = 5
    return p.n


def maybe_error_leaky_subclass() -> int:
    c = LeakySub()
    c.extra = 5
    return c.n
