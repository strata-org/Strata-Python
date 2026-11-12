# Test: another module rebinds the marker that li_m_outside_target.py imported. CPython calls the
# new value at the marker call and prints "called"; the guard in li_m_outside_target's translation
# reads the new value and stops there (docs/PythonToDyn.md §6.11). The machine stops with a gap at
# the import of the program module first.
import li_m_outside_target as m

m.loop_invariant = lambda p: print("called")
print(m.f(3))
