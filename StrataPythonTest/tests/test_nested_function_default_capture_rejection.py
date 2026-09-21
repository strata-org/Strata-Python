def outer() -> int:
    limit = 5

    def clamp(value: int = limit) -> int:
        return value

    return clamp()


outer()
