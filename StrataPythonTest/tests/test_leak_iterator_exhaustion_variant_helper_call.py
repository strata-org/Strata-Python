"""A helper-raised StopIteration is consumed inside __next__."""


def transform(value):
    if value == 2:
        raise StopIteration("transform failed")
    return value


class Transformed:
    def __init__(self, source):
        self.iterator = iter(source)

    def __iter__(self):
        return self

    def __next__(self):
        return transform(next(self.iterator))


RESULT = list(Transformed([1, 2, 3]))


if __name__ == "__main__":
    print(repr(RESULT))
