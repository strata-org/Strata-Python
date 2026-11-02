# Test: set operators on sets of plain user objects, and a set that mixes them with an int
class P:
    pass
p1 = P()
p2 = P()
p3 = P()
a = {p1, p2}
b = {p2, p3}
print(a & b == {p2}, a - b == {p1}, a <= {p1, p2, p3}, a == {p2, p1}, a != b)
c = {p1, 1}
print(c == {1, p1})
