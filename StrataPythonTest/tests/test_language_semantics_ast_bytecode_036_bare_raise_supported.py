# Bare raise in nested handlers re-raises innermost.
"""Bare raise in nested handlers re-raises innermost."""
try:
    try:
        raise ValueError('outer')
    except ValueError:
        try:
            raise TypeError('inner')
        except TypeError:
            raise  # re-raises TypeError, not ValueError
except TypeError as e:
    assert str(e) == 'inner'
    print('PASS')
