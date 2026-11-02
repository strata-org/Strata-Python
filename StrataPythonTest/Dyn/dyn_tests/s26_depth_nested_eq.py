# Test: nested comparisons and user __eq__ calls share one C recursion count
def nest(x, k):
    while k > 0:
        x = [x]
        k = k - 1
    return x
class E:
    def __init__(self, n):
        self.n = n
    def __eq__(self, other):
        if self.n == 0:
            return True
        return nest(E(self.n - 1), 500) == nest(E(self.n - 1), 500)
print(nest(E(15), 500) == nest(E(15), 500))
print(nest(E(25), 500) == nest(E(25), 500))
