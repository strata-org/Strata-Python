# Boundary: raise from None suppresses context display.
"""Boundary: raise from None suppresses context display."""
try:
    try:
        raise ValueError('hidden')
    except ValueError:
        raise TypeError('visible') from None
except TypeError as e:
    # __context__ is still set (it always is), but __suppress_context__ hides it
    assert e.__context__ is not None  # still linked
    assert e.__suppress_context__ == True  # but suppressed
    assert e.__cause__ is None
    print('PASS: from None suppresses context (naive model might lose __context__ entirely)')
