# The repr of a copy by |, which keeps its source's hole in CPython, while a value's __repr__
# resizes it: CPython's repr loses entries; the model, whose copy drops the hole, stops with a gap.
class A:
    def __init__(self, v):
        self.v = v
    def __repr__(self):
        c[200] = 0
        c[201] = 0
        return "A%d" % self.v
a = {0: 0, 1: A(1), 2: A(2), 3: A(3)}
del a[0]
c = a | {}
print(repr(c))
