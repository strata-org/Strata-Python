# Test: an instance of a subclass of super with its own __get__, read as a class attribute
class S(super):
    def __get__(self, obj, owner=None):
        return 42
class B:
    pass
class C:
    x = S(B, B())
r = C().x
