# Test: e.args = UserIter() needs a loop of user code inside an attribute write, and stops with a gap
class U:
    def __iter__(self):
        return self
    def __next__(self):
        raise StopIteration
e = ValueError(1)
e.args = U()
print(len(e.args))
