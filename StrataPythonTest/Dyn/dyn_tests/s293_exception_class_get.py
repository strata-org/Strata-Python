# Test: an exception whose class defines __get__, read as a class attribute
class E(Exception):
    def __get__(self, obj, owner=None):
        return 42
class C:
    x = E()
r = C().x
