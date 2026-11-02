# Test: a __dict__ slot below an exception class, whose instances already have a dict
class E(Exception):
    __slots__ = ()
class F(E):
    __slots__ = ('__dict__',)
