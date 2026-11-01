# Test: a set lookup with two members of the probe's hash compares them in an order that the layout decides
class Q:
    def __init__(self, n):
        self.n = n
    def __hash__(self):
        return 7
    def __eq__(self, o):
        print("Q", self.n, "eq")
        return self.n == 1 and o.n == 9
q1, q2 = Q(1), Q(2)
s = {q1, q2, "a", "b", "c", "d"}
print(Q(9) in s)
