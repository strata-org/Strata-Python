# Chained assign: mutations visible through both names.
"""Chained assign: mutations visible through both names."""
x = y = z = {'key': 'val'}
x['new'] = 1
assert y == {'key': 'val', 'new': 1}
assert z is x is y
print('PASS')
