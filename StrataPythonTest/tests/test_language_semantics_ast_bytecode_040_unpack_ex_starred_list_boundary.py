# Boundary: starred target from tuple source is list, not tuple.
"""Boundary: starred target from tuple source is list, not tuple."""
source = (10, 20, 30, 40)
first, *middle, last = source

# Naive model might preserve source type (tuple)
assert type(middle) is list, f'got {type(middle)}'
assert middle == [20, 30]
print('PASS: starred target is list even from tuple source (naive type-preserving model fails)')
