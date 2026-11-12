from pyhard import loop_invariant, OLD
def f(c):
    with c as loop_invariant:
        pass
