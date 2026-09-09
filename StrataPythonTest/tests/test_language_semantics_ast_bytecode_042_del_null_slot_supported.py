# Del makes slot NULL; re-assignment works.
"""Del makes slot NULL; re-assignment works."""
def f():
    x = 1
    del x
    x = 2  # re-assign after del
    return x

assert f() == 2
print('PASS')
