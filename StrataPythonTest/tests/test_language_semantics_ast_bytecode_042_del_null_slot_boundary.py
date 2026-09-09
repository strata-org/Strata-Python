# Boundary: del raises UnboundLocalError, not NameError.
"""Boundary: del raises UnboundLocalError, not NameError."""
x = 'global'
def f():
    x = 'local'
    del x
    try:
        return x  # does NOT fall through to global
    except UnboundLocalError:
        return 'UnboundLocalError'
    except NameError:
        return 'NameError'

assert f() == 'UnboundLocalError'
print('PASS: UnboundLocalError not NameError (naive model might fall through to global)')
