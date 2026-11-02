# Test: a __dict__ slot below a built-in class written in Python, whose instances already have a dict
class H(type(help)):
    __slots__ = ('__dict__',)
