# Test: del on an object whose class defines only __setitem__, by key and by slice
class L:
    def __setitem__(self, k, v):
        print("set", k, v)
x = L()
x[0] = 1
try:
    del x[0]
except AttributeError as e:
    print("AttributeError", e.args[0])
except TypeError:
    print("TypeError")
try:
    del x[1:2]
except AttributeError as e:
    print("AttributeError", e.args[0])
except TypeError:
    print("TypeError")
