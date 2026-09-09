"""Case 3 (yield from): A plain iterator injects an exhaustion value."""


class SneakyIterator:
    def __init__(self):
        self.index = 0

    def __iter__(self):
        return self

    def __next__(self):
        self.index += 1
        if self.index > 2:
            raise StopIteration("attacker-controlled")
        return self.index


INJECTED = []


def outer():
    value = yield from SneakyIterator()
    INJECTED.append(value)


YIELDED = list(outer())
RESULT = YIELDED, INJECTED[0]


if __name__ == "__main__":
    print(repr(RESULT))
