from pyhard import loop_invariant, OLD
def f():
    loop_invariant = 1
    def g():
        nonlocal loop_invariant
        loop_invariant = 2
    return g
