def outer(flag: bool) -> int:
    if flag:
        def conditional() -> int:
            return 1
        return conditional()
    return 0


outer(True)
