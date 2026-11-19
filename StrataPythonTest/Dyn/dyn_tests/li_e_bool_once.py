# Test: an invariant holds when `if P:` would take its true branch, so the __bool__ of an `and`
# operand runs once per evaluation, not again on the result: when DynInvariantEvalTest checks it,
# it is False, True and False at the three head entries (bool 1, 2 and 3).
from pyhard import loop_invariant

class Flip:
    def __init__(self):
        self.n = 0

    def __bool__(self):
        self.n += 1
        print("bool", self.n)
        return self.n % 2 == 0

def f(a, n):
    i = 0
    loop_invariant(lambda: a and i >= 0)
    while i < n:
        i += 1
    return i

print(f(Flip(), 2))
