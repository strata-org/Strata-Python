def helper() -> int:
    return 1


def outer() -> int:
    value = helper()

    def helper() -> int:
        return 2

    return value


outer()
