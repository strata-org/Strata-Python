# A copy by | keeps the hole of its source in CPython (a fast copy), so the comparison of the copy
# may lose its place after a resize; the model, whose copy drops the hole, stops with a gap.
class A:
    def __init__(self, v):
        self.v = v
    def __eq__(self, other):
        print("eq", self.v)
        c[200] = 0
        c[201] = 0
        return True
a = {0: 0, 1: A(1), 2: A(2), 3: A(3)}
del a[0]
c = a | {}
b = {1: A(1), 2: A(2), 3: A(3)}
print(c == b)
