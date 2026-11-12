# A __repr__ that is a property whose getter raises: CPython drops the exception and gives the
# default repr, which shows the object's address; the model stops with a gap.
class A:
    @property
    def __repr__(self):
        raise KeyError("k")
print(repr(A()).startswith("<"))
