# Test: a set display of constants, whose order the model doesn't assume, stops with a gap when it is iterated
for x in {7, 15}:
    print(x)
s = {1, 9, 17, 25, 33, 2}
for x in s:
    print(x)
t = {7, 15}
for x in t:
    print(x)


class K:
    def __hash__(self):
        return -2

    def __eq__(self, other):
        print("eq", other)
        return False


print(K() in {-1, -2})
x = "a"
print(x in {"a", "b"})
