# Test: an uncaught exception whose class defines __str__ stops with a gap in the outcome
class E(Exception):
    pass
E.__str__ = lambda self: "custom"
raise E(5)
