"""Case 6 (legacy iteration): __getitem__ consumes accidental IndexError."""


class Table:
    def __init__(self, rows, widths):
        self.rows = rows
        self.widths = widths

    def __getitem__(self, index):
        row = self.rows[index]
        return row[:self.widths[index]]


RESULT = list(Table(["aaa", "bbb", "ccc"], [1, 2]))


if __name__ == "__main__":
    print(repr(RESULT))
