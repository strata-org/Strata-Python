# CPython renames nothing at module level, nor in a class named only with underscores.
__T = int

def f(x: __T) -> None:
    ...

class _:
    __x: int
