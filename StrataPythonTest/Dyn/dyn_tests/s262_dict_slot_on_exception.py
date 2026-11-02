# Test: a __dict__ slot on an exception class, whose instances already have a dict
class E(Exception):
    __slots__ = ('__dict__',)
