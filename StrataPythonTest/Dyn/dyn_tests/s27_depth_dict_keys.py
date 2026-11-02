# Test: dicts with keys nested 899 deep, compared under 800 nested user __eq__ calls
def nest(x, k):
    while k > 0:
        x = [x]
        k = k - 1
    return x
def tup(k):
    x = ()
    while k > 0:
        x = (x,)
        k = k - 1
    return x
class E:
    def __init__(self, n, depth):
        self.n = n
        self.depth = depth
    def __eq__(self, other):
        if self.n == 0:
            return {tup(899): 1} == {tup(899): 1}
        return nest(E(self.n - 1, self.depth), self.depth) == nest(E(self.n - 1, self.depth), self.depth)
print(nest(E(800, 6), 6) == nest(E(800, 6), 6))
print(nest(E(800, 9), 9) == nest(E(800, 9), 9))
