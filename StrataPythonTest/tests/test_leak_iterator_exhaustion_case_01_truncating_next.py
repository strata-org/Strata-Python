"""Case 1 (iterator exhaustion): StopIteration escaping __next__ truncates."""


class Pairs:
    def __init__(self, source):
        self.iterator = iter(source)

    def __iter__(self):
        return self

    def __next__(self):
        left = next(self.iterator)
        right = next(self.iterator)
        return left, right


RESULT = list(Pairs([1, 2, 3]))


if __name__ == "__main__":
    print(repr(RESULT))
