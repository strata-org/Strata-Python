# Test: isinstance with a metaclass's __instancecheck__, alone and in a tuple, and with a tuple of int and str
class M(type):
    def __instancecheck__(cls, obj):
        return True
class A(metaclass=M):
    pass
print(isinstance(1, A), isinstance(1, (str, A)), isinstance("a", (int, str)))
