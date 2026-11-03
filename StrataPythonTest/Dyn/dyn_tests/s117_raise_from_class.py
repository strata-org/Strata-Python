# Test: raise from an exception class stops with a gap
e = ValueError("v")
class C(Exception):
    def __init__(self):
        print("C sees", e.__context__ is None)
try:
    try:
        raise KeyError("k")
    except KeyError:
        raise e from C
except ValueError as t:
    print(type(t.__cause__).__name__)
