class Counter:
    def __init__(self):
        self.n: int = 0


counter: Counter = Counter()


def increment():
    counter.n += 1
