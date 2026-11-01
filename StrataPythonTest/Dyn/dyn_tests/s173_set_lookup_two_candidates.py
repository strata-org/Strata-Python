# Test: a set lookup among two members of the probe's hash; the model stops earlier, where building the set compares the second member with the first in a layout that depends on the hash seed
class Q:
    def __init__(self, n):
        self.n = n
    def __hash__(self):
        return 7
    def __eq__(self, o):
        print("Q", self.n, "eq")
        return self.n == 1 and o.n == 9
q1, q2 = Q(1), Q(2)
s = {"a", "b", q1, q2, "c", "d"}
print(Q(9) in s)
