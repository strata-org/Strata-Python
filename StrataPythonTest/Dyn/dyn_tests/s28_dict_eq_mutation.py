# Test: a value's __eq__ that changes the dict while == walks it
class V:
    def __init__(self, n, d):
        self.n = n
        self.d = d
    def __eq__(self, other):
        print("eq", self.n)
        if self.n == 1:
            del self.d["c"]
            self.d["z"] = 9
        return True
a = {}
b = {}
a["a"] = V(1, a)
a["b"] = V(2, a)
a["c"] = V(3, a)
b["a"] = 0
b["b"] = 0
b["c"] = 0
print(a == b, "z" in a, "c" in a)
