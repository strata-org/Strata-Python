# Test: set operators whose comparisons run user __eq__, walking the live tables in CPython's order
class K:
    def __init__(self, n):
        self.n = n
    def __hash__(self):
        return self.n % 4
    def __eq__(self, other):
        print("eq", self.n, other.n)
        return self.n == other.n
k1 = K(1)
k5 = K(5)
k2 = K(2)
a = {k1, k2}
b = {K(5), K(2)}
print("and")
c = a & b
print("sub")
d = a - b
print("le")
print(a <= b)
print("or")
a |= {K(9)}
print("xor")
a ^= {K(1)}
print("isub")
a -= {K(13)}
print("eq")
print(a == {K(2)})
print("mutation")
class M:
    def __init__(self, n):
        self.n = n
    def __hash__(self):
        return self.n % 4
    def __eq__(self, other):
        print("eq", self.n, other.n)
        global a
        if self.n == 5:
            a -= {k2}
            a |= {M(3)}
        return self.n == other.n
k1 = M(1)
k2 = M(2)
a = {k1, k2}
b = {M(5), M(2)}
d = a - b
print(k1 in d, k2 in d)
