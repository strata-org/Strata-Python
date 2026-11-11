# A list subclass extended by itself, whose __iter__ gives a user iterator, stops with a gap;
# CPython gathers the iterator's items first, and gives [1, 2, 1, 0].
class It:
    def __init__(self):
        self.n = 2

    def __iter__(self):
        return self

    def __next__(self):
        if self.n == 0:
            raise StopIteration
        self.n -= 1
        return self.n


class L(list):
    def __iter__(self):
        return It()


x = L([1, 2])
x.extend(x)
print(list.__repr__(x))
