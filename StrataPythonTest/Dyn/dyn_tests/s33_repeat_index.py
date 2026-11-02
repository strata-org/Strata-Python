# Test: repetition counts, indices and slice bounds converted by their type's __index__
class P:
    def __index__(self):
        return 2
a = [1] * P()
b = P() * "ab"
c = (3,) * P()
print(a == [1, 1], b, c == (3, 3))
l = [10, 20, 30]
print(l[P()], (10, 20)[P()], "ab"[P()], l[P():] == [20, 30], "abc"[:P()])
l[P()] = 5
del l[P()]
print(l[0], l[1])
class Q:
    def __index__(self):
        return "x"
[1] * Q()
