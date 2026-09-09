# Starred target from various iterable types.
"""Starred target from various iterable types."""
# From tuple
a, *b = (1, 2, 3)
assert type(b) is list and b == [2, 3]

# From string
x, *y = 'hello'
assert type(y) is list and y == ['e', 'l', 'l', 'o']

# From range
first, *rest = range(5)
assert type(rest) is list and rest == [1, 2, 3, 4]

# Empty starred
a, *b, c = [1, 2]
assert b == []  # still a list, just empty
assert type(b) is list

print('PASS')
