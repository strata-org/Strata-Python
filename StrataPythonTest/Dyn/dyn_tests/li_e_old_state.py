# Test: OLD reads state that the function changes before its loop: a rebound parameter, a list
# that grows, a global and a nonlocal, so that reading the current state in place of the entry
# state gives other answers.
from pyhard import loop_invariant, OLD

g = 1

def outer(c):
    def f(a, xs):
        global g
        nonlocal c
        i = 0
        a = a + 10
        xs.append(0)
        g = g + 1
        c = c + 1
        loop_invariant(lambda: a == OLD(a) + 10)
        loop_invariant(lambda: len(xs) == OLD(len(xs)) + 1)
        loop_invariant(lambda: g == OLD(g) + 1 and c == OLD(c) + 1)
        loop_invariant(lambda: i < OLD(a))
        while i < 3:
            i += 1
        return i
    return f(2, [1])

print(outer(5))
