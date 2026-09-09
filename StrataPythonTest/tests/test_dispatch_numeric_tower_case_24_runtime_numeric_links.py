"""Runtime MRO, annotation widening, and result tags are distinct relations."""


RESULT = (
    tuple(item.__name__ for item in bool.__mro__),
    tuple(item.__name__ for item in int.__mro__),
    tuple(item.__name__ for item in float.__mro__),
    issubclass(bool, int),
    issubclass(int, float),
    isinstance(1, float),
    type(True + True).__name__,
    type(True & True).__name__,
    type(True & 1).__name__,
)
