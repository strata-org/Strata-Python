# Boundary: splats are NOT grouped before regular elements.
"""Boundary: splats are NOT grouped before regular elements."""
order = []
def first(): order.append('first'); return [10]
def middle(): order.append('middle'); return 20
def last(): order.append('last'); return [30]

# A naive model might evaluate all *splats first, then regular elements
result = [*first(), middle(), *last()]
assert order == ['first', 'middle', 'last'], f'got {order}'
print('PASS: splats not hoisted (naive grouping model would get [first, last, middle])')
