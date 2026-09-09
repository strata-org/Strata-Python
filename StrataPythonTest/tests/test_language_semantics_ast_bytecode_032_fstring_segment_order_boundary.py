# Boundary: format spec evaluated AFTER main expr, not before.
"""Boundary: format spec evaluated AFTER main expr, not before."""
order = []
val = [0]
def expr():
    val[0] = 42
    order.append('expr')
    return val[0]
def spec():
    order.append('spec')
    # If spec were evaluated first, val[0] would still be 0
    return 5 if val[0] == 42 else 1

result = f"{expr():{spec()}}"
assert order == ['expr', 'spec'], f'got {order}'
# spec sees val[0]==42 because expr ran first
assert result == '   42', f'got {result!r}'
print('PASS: format spec sees side effects of main expression')
