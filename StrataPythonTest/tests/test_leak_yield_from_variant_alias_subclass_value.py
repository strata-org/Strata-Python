"""Aliases and subclasses do not change yield-from value injection."""

Sentinel = StopIteration


class Done(Sentinel):
    pass


class Iterator:
    def __iter__(self):
        return self

    def __next__(self):
        raise Done("subclass-controlled")


CAPTURED = []


def outer():
    CAPTURED.append((yield from Iterator()))


YIELDED = list(outer())
RESULT = YIELDED, CAPTURED[0]


if __name__ == "__main__":
    print(repr(RESULT))
