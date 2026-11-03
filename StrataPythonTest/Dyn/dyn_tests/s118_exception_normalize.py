# Test: an exception class whose call gives an exception of another class stops with a gap
class B(Exception):
    def __new__(cls, *a):
        if a:
            print("normalized")
            return Exception("n")
        return KeyError("k")
try:
    raise B
except BaseException as e:
    print(type(e).__name__)
