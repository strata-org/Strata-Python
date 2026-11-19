# Test: the head entries of loops of several shapes: a one-line while, a test over several lines,
# a for over an iterable whose evaluation changes what P reads, an iterable and a target over
# several lines, a loop in a method, and an invariant whose P reads a property whose getter runs a
# loop with its own invariant.
from pyhard import loop_invariant

count = 0

def items(n):
    global count
    count = 10
    return [(0, 0), (1, 1), (2, 2)]

def f(n):
    i = 0
    loop_invariant(lambda: i <= n)
    while i < n: i += 1
    j = 0
    loop_invariant(lambda: j <= n)
    while (j < n
           and j >= 0):
        j += 1
    total = 0
    loop_invariant(lambda: count == 10)
    for x in items(n):
        total += x[0]
    pairs = 0
    loop_invariant(lambda: pairs >= 0)
    for (a,
         b) in items(
            n):
        pairs += 1
    return i + j + total + pairs

class C:
    @property
    def size(self):
        s = 0
        loop_invariant(lambda: s <= 2)
        while s < 2:
            s += 1
        return s

    def m(self, n):
        k = 0
        loop_invariant(lambda: k <= n)
        loop_invariant(lambda: self.size == 2)
        for _ in range(n):
            k += 1
        return k

print(f(3), C().m(2))
