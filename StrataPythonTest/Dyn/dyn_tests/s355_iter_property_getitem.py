# An __iter__ property whose getter raises, on a class that also has __getitem__: CPython clears
# the getter's exception and iterates by __getitem__; the model stops with a gap.
class B:
    @property
    def __iter__(self):
        raise KeyError("k")
    def __getitem__(self, i):
        if i < 2:
            return i
        raise IndexError
for x in B():
    print(x)
