"""The module docstring."""
# The module body writes __name__ and __doc__; reads and dels of the other module attributes
# CPython defines are rejected, and so is a write to __builtins__.
doc = __doc__


def f():
    return __name__, __doc__, __spec__, __package__, __loader__


def g(__file__):
    return __file__


print(__file__, __cached__, __builtins__, __annotations__, __path__)
del __file__
__builtins__ = {}
