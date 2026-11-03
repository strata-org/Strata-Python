# A looping built-in reached inside an operation: a built-in iterator finishes, a user one stops.
class U:
    def __init__(self):
        self.i = 0

    def __iter__(self):
        return self

    def __next__(self):
        self.i += 1
        if self.i > 3:
            raise StopIteration
        return self.i // 3


class C:
    __radd__ = staticmethod(any)


print(sum([C()], iter([0, 0, 1])))
print(sum([C()], U()))
