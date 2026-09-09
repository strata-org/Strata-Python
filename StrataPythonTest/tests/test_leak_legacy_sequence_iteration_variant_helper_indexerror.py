"""IndexError raised by a helper is consumed by legacy iteration."""


def width_at(widths, index):
    return widths[index]


class Table:
    def __init__(self):
        self.rows = ["aaa", "bbb", "ccc"]
        self.widths = [1, 2]

    def __getitem__(self, index):
        return self.rows[index][:width_at(self.widths, index)]


RESULT = list(Table())


if __name__ == "__main__":
    print(repr(RESULT))
