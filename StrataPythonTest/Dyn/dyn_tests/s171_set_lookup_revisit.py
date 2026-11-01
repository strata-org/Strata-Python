# Test: a set lookup whose layout depends on the hash seed may compare one member several times
n = 0
class K:
    def __hash__(self):
        return -2
    def __eq__(self, o):
        global n
        n += 1
        return False
r = K() in {"a", "b", "c", -2}
print(r, n)
