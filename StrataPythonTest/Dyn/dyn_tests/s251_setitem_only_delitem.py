# Test: an item write on an object whose class defines only __delitem__ raises AttributeError
class L:
    def __delitem__(self, k):
        pass
L()[1] = 2
