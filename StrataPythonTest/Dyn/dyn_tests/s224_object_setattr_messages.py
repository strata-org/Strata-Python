# Test: object.__setattr__ and object.__delattr__ messages, in CPython's order of checks
class M(type):
    pass
class A(metaclass=M):
    pass
class B:
    pass
try:
    object.__setattr__(A, 'x', 1)
except TypeError as e:
    print("1", e.args[0])
try:
    object.__setattr__(B, 1, 2)
except TypeError as e:
    print("2", e.args[0])
try:
    object.__setattr__(B(), 'x')
except TypeError as e:
    print("3", e.args[0])
try:
    object.__delattr__(A, 'x')
except TypeError as e:
    print("4", e.args[0])
try:
    object.__getattribute__(B(), 1)
except TypeError as e:
    print("5", e.args[0])
try:
    object.__setattr__(B(), 'x')
except TypeError as e:
    print("6", e.args[0])
