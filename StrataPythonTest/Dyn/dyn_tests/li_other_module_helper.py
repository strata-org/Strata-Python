# Test: a module that defines its own loop_invariant, which li_other_module.py imports and calls
# as an ordinary function.
def loop_invariant(p):
    print("not pyhard's loop_invariant")
