# Test: %d of a value whose __int__ returns a bool, where CPython 3.12 warns
class N:
    def __int__(self):
        return True
r = "%d" % N()
