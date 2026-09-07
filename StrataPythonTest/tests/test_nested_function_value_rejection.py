def outer() -> int:
    def inner() -> int:
        return 1

    alias = inner
    return 0


outer()
