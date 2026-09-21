def outer(x: int) -> int:
    bonus: int = 10

    def inner(y: int) -> int:
        return x + y + bonus

    return inner(5)


def late_binding() -> int:
    x = 1

    def read() -> int:
        return x

    x = 2
    return read()


def chain(x: int) -> int:
    def middle() -> int:
        def leaf() -> int:
            return x
        return x + leaf()

    return middle()


def countdown(limit: int) -> int:
    def step(n: int) -> int:
        if n >= limit:
            return n
        return step(n + 1)

    return step(0)


assert outer(1) == 16
assert late_binding() == 2
assert chain(3) == 6
assert countdown(3) == 3
