# Test: del on a class whose metaclass defines only __setitem__
class M(type):
    def __setitem__(cls, k, v):
        print("meta set", k, v)
class A(metaclass=M):
    pass
A[1] = 2
try:
    del A[1]
except AttributeError as e:
    print("AttributeError", e.args[0])
