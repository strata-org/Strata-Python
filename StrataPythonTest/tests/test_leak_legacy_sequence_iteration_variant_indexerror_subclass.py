"""A subclass of IndexError also terminates legacy sequence iteration."""


class EndOfTable(IndexError):
    pass


class Table:
    def __getitem__(self, index):
        if index == 2:
            raise EndOfTable("accidental")
        return index


RESULT = list(Table())


if __name__ == "__main__":
    print(repr(RESULT))
