# Test: the checks of a built-in __new__ called on another class
try:
    BaseException.__new__(int)
except TypeError as e:
    print(e.args[0])
try:
    BaseException.__new__(1)
except TypeError as e:
    print(e.args[0])
try:
    x = ValueError.__new__(KeyError, "x")
    print(type(x).__name__)
except TypeError as e:
    print(e.args[0])
try:
    x = BaseException.__new__(OSError, 2, "x")
    print(type(x).__name__, x.errno)
except TypeError as e:
    print(e.args[0])
class E(ValueError):
    def __new__(cls, *a):
        return super().__new__(cls, *a)
e = E(1, 2)
print(e.args[0], e.args[1])
try:
    x = property.__new__(int)
    print(type(x).__name__)
except TypeError as e:
    print(e.args[0])
try:
    x = OSError.__new__(ValueError, 2, "x")
    print(type(x).__name__)
except TypeError as e:
    print(e.args[0])
