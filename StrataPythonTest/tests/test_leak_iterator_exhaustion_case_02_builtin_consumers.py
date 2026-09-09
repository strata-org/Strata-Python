"""Case 2 (iterator exhaustion): Built-ins accept a truncated iterator."""


class Every:
    def __init__(self, source, table):
        self.iterator = iter(source)
        self.table = table

    def __iter__(self):
        return self

    def __next__(self):
        value = next(self.iterator)
        scale = next(self.table)
        return value * scale


def make_iterator():
    return Every([1, 2, 3, 4], iter([10, 10]))


RESULT = {
    "list": list(make_iterator()),
    "zip": list(zip(make_iterator(), "abcd")),
    "sum": sum(make_iterator()),
    "max": max(make_iterator(), default="<empty>"),
}


if __name__ == "__main__":
    print(repr(RESULT))
