class Counter:
    def __init__(self):
        self.n: int = 0


counter: Counter = Counter()


def reset():
    counter.n = 0
