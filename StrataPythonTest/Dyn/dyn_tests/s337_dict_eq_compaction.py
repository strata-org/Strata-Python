# A value's __eq__ that adds keys to the dict being compared, after a deletion from it: CPython's
# resize compacts the dict's entries and moves those that the comparison hasn't reached yet, which
# the model doesn't follow, so the run stops with a gap.
class A:
    def __init__(self, v):
        self.v = v
    def __eq__(self, other):
        print("eq", self.v)
        for i in range(30):
            a[100 + i] = 0
        return True
    def __hash__(self):
        return 0
a = {0: 0, 1: A(1), 2: A(2), 3: A(3)}
del a[0]
b = {1: A(1), 2: A(2), 3: A(3)}
print(a == b)
