# A constructor reached inside another operation, over a user iterator, stops with a gap.
class It:
    def __init__(self):
        self.n = 3

    def __iter__(self):
        return self

    def __next__(self):
        if self.n == 0:
            raise StopIteration
        self.n -= 1
        return self.n


class U:
    p = property(frozenset)

    def __iter__(self):
        return It()


print("before")
x = U().p
