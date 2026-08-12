class Counter:
    def __init__(self):
        self.n: int = 0


counter: Counter = Counter()


def read_n() -> int:
    return counter.n
