def outer(x: int) -> int:
    local = 1

    def captures_param() -> int:
        return x

    def captures_local() -> int:
        return local

    return captures_param() + captures_local()


outer(3)
