"""A StopIteration subclass is also consumed as iterator exhaustion."""


class Done(StopIteration):
    pass


class Items:
    def __init__(self):
        self.index = 0

    def __iter__(self):
        return self

    def __next__(self):
        self.index += 1
        if self.index == 2:
            raise Done("not ordinary exhaustion")
        return self.index


RESULT = list(Items())


if __name__ == "__main__":
    print(repr(RESULT))
