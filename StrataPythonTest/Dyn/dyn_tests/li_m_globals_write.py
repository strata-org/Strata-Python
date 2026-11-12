# Test: a write of a marker name through globals(), which the translator can't see. CPython calls
# the new value and prints "called"; the guard before the loop reads the new value and stops
# unless it is the marker (docs/PythonToDyn.md §6.11), and the machine stops with a gap at
# globals() first.
from pyhard import loop_invariant

def f(n):
    i = 0
    loop_invariant(lambda: i >= 0)
    while i < n:
        i += 1
    return i

globals()["loop_invariant"] = lambda p: print("called")
print(f(1))
