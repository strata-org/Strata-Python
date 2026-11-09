# Test: a loop over a user iterator inside another operation's step stops with a gap
class It:
    def __iter__(self):
        return self
    def __next__(self):
        raise StopIteration
l = [1, 2]
l[:] = It()
print(len(l))
