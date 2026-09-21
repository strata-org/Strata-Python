def outer() -> int:
    count = 0

    def bump() -> None:
        nonlocal count
        count = count + 1

    bump()
    return count


outer()
