# A __getitem__ iterator whose __len__ ends it: __length_hint__ stops with a gap, where CPython
# gives len() less the index the ended iterator kept.
class D:
    def __getitem__(self, i):
        raise IndexError
    def __len__(self):
        next(D.it, None)
        return 5
D.it = iter(D())
print(D.it.__length_hint__())
print(D.it.__length_hint__())
