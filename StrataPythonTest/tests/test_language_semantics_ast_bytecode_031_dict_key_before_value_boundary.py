# Boundary: a naive model evaluating value-before-key (pre-3.8 behavior) gets
# wrong order.
"""Boundary: a naive model evaluating value-before-key (pre-3.8 behavior) gets wrong order."""
order = []
state = {'count': 0}
def k():
    state['count'] += 1
    order.append(f"k{state['count']}")
    return state['count']
def v():
    order.append(f"v{state['count']}")
    return state['count'] * 10

# If key is evaluated first, v() sees the updated count
# If value were evaluated first (pre-3.8), v() would see stale count
d = {k(): v()}
assert order == ['k1', 'v1'], f'got {order}'
assert d == {1: 10}, f'got {d}'
print('PASS: key-before-value confirmed (naive value-first model would get {0: 0})')
