# Test: an item deletion on an object whose class defines only __setitem__ raises AttributeError
class L:
    def __setitem__(self, k, v):
        pass
del L()[0]
