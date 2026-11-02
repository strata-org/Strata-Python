# Test: __init_subclass__ called with a positional argument raises CPython's TypeError
class C:
    pass
C.__init_subclass__(1)
