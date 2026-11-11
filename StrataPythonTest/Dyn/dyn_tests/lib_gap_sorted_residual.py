# sorted reached through __radd__ inside sum's step, over a user iterator, stops with the gap of
# a looping built-in inside an operation; CPython gives [0, 1, 2].
class U:
    def __init__(self):
        self.n = 3

    def __iter__(self):
        return self

    def __next__(self):
        if self.n == 0:
            raise StopIteration
        self.n -= 1
        return self.n


class C:
    __radd__ = staticmethod(sorted)


print(sum([C()], U()))
