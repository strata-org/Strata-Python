def outer(x: int) -> int:
    def reads_x() -> int:
        return x

    def calls_reads_x() -> int:
        return reads_x()

    return calls_reads_x()


outer(1)
