# Test: in on an object whose class sets __contains__ to None raises TypeError
class C:
    __contains__ = None
1 in C()
