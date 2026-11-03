# A reversed whose sequence's class lost __getitem__ stops with a gap.
class S:
    def __len__(self):
        return 2

    def __getitem__(self, i):
        return i


r = reversed(S())
print(next(r))
del S.__getitem__
next(r)
