# Boundary: bare raise outside handler is RuntimeError.
"""Boundary: bare raise outside handler is RuntimeError."""
try:
    raise  # no active exception
except RuntimeError as e:
    assert 'No active exception' in str(e)
    print('PASS: bare raise outside handler raises RuntimeError')
