# Dict key-before-value: key side effects happen first.
"""Dict key-before-value: key side effects happen first."""
order = []
def make_key(n): order.append(f'k{n}'); return n
def make_val(n): order.append(f'v{n}'); return n * 10

d = {make_key(1): make_val(1), make_key(2): make_val(2)}
assert order == ['k1', 'v1', 'k2', 'v2']
assert d == {1: 10, 2: 20}
print('PASS')
