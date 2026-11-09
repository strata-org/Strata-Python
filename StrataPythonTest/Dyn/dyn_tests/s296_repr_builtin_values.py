# Test: repr and str of built-in values, containers and a list and a dict that contain themselves
print(repr(1), repr(-2.5), repr("a'b"), repr(b"x\n"), repr(None), repr(True))
print([1, "a", (2,), (3, 4), [], {}], {1: "x", "k": [2]}, (1,))
class G:
    def __getitem__(self, k):
        return k
print(range(3), range(1, 10, 2), G()[1::2], ..., NotImplemented)
print(int, list, repr(len), str, type)
x = [1]
x += [x]
print(x)
d = {}
d["self"] = d
print(d)
n = 5
print({n}, {n} - {n})
