def outer(x: int) -> int:
    def middle() -> int:
        def leaf() -> int:
            return x
        return leaf()
    return middle()


outer(3)
