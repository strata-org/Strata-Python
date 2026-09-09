"""StopIteration.value can originate in a helper called by __next__."""


def finish():
    raise StopIteration("helper-controlled")


class Iterator:
    def __init__(self):
        self.first = True

    def __iter__(self):
        return self

    def __next__(self):
        if self.first:
            self.first = False
            return 1
        return finish()


CAPTURED = []


def outer():
    CAPTURED.append((yield from Iterator()))


YIELDED = list(outer())
RESULT = YIELDED, CAPTURED[0]


if __name__ == "__main__":
    print(repr(RESULT))
