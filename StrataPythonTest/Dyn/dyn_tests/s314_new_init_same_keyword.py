# Test: one keyword argument that a class call passes to both __new__ and __init__
class D:
    def __new__(cls, a):
        return object.__new__(cls)
    def __init__(self, a):
        self.a = a
d = D(a=1)
print(d.a)
