# Test: item assignment on an object whose class defines only __delitem__
class L:
    def __delitem__(self, k): pass
try:
    L()[1] = 2
except AttributeError:
    print("AttributeError")
except TypeError:
    print("TypeError")
