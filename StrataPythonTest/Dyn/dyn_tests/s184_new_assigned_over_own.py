# Test: a built-in's __new__ assigned over a class's own __new__, which keeps slot_tp_new in CPython
class C(Exception):
    def __new__(cls, *a):
        return super().__new__(cls, *a)
C.__new__ = ValueError.__new__
C(1)
print("reached")
