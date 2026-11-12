# Test: a loop whose marker another module rebinds (li_m_outside_write.py), which this module's
# translator can't see: the guard before the loop reads the module's global loop_invariant
# (docs/PythonToDyn.md §6.11).
from pyhard import loop_invariant

def f(n):
    i = 0
    loop_invariant(lambda: 0 <= i <= n)
    while i < n:
        i += 1
    return i

print(f(2))
