"""Case 10 (finally override): Abrupt control discards a sentinel."""


def swallowed_by_return():
    try:
        raise StopIteration("pending return")
    finally:
        return "returned"


def swallowed_by_break():
    while True:
        try:
            raise StopIteration("pending break")
        finally:
            break
    return "loop exited"


def swallowed_by_continue():
    visited = []
    for index in range(1):
        try:
            raise StopIteration("pending continue")
        finally:
            visited.append(index)
            continue
    return visited


RESULT = (
    swallowed_by_return(),
    swallowed_by_break(),
    swallowed_by_continue(),
)


if __name__ == "__main__":
    print(repr(RESULT))
