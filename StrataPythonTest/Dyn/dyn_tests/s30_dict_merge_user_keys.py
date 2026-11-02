# Test: dict | and |= with keys that are plain user objects, and with a key whose __eq__ is a user's
class P:
    pass
p1 = P()
p2 = P()
a = {p1: 1}
b = {p2: 2, p1: 3}
c = a | b
a |= b
print(c[p1], c[p2], a[p1], a[p2])
class K:
    def __hash__(self):
        return 1
    def __eq__(self, other):
        return self is other
k = K()
d = {k: 1}
d |= {1: 2}
