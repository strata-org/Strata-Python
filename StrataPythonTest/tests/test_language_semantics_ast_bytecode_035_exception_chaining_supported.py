# Exception chaining: __cause__ via 'raise from'.
"""Exception chaining: __cause__ via 'raise from'."""
orig = ValueError('orig')
try:
    raise TypeError('new') from orig
except TypeError as e:
    assert e.__cause__ is orig
    assert e.__suppress_context__ == True
    print('PASS')
