# The symmetric difference of two items views, while a value's __eq__ adds keys to the second
# dict, which has a deleted entry, stops with a gap: CPython's resize then moves the entries under
# the walk.
class A:
    def __init__(self, v):
        self.v = v

    def __eq__(self, other):
        for i in range(30):
            d2[100 + i] = 0
        return self.v == other.v

    def __hash__(self):
        return 0


d2 = {0: 0, 1: A(2), 3: 0, 4: 0}
del d2[0]
d1 = {1: A(1), 3: 1}
print(len(d1.items().__xor__(d2.items())))
