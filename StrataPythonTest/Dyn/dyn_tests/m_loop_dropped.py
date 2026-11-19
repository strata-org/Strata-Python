# A loop in an `except` clause of a `try` whose body cannot raise: the builder drops the loop's
# blocks, so `f` has no record of it.  `g`'s `while True: pass` keeps its record and its `done`,
# because the translator lowers its test with `py.truthy`, which has a raise edge to `done`.
def f():
    try:
        pass
    except ValueError:
        while c():
            pass
    return 0

def g():
    while True:
        pass
