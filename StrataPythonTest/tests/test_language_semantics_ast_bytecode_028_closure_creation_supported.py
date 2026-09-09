# Closure captures live cell, not snapshot
def make_adder(n):
    def add(x): return x + n
    return add
add5 = make_adder(5)
assert add5(3) == 8
print("OK: closure creation — captures cell correctly")
