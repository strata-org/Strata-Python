# Boundary: naive model assuming independent copies would diverge.
"""Boundary: naive model assuming independent copies would diverge."""
a = b = []
a.append(42)
# If copies were made, b would still be []
assert b == [42], f'got {b}'
assert a is b  # reference identity, not value equality
print('PASS: not independent copies (naive copy model would get b==[])')
