# Test: an attribute write on an instance whose class sets __setattr__ to dict.__setitem__ raises TypeError
class C:
    __setattr__ = dict.__setitem__
c = C()
c.x = 1
print("set")
