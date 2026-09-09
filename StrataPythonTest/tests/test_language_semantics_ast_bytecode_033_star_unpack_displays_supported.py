# Star-unpacking in displays: interleaved evaluation.
"""Star-unpacking in displays: interleaved evaluation."""
order = []
def x(): order.append('x'); return {'a': 1}
def y(): order.append('y'); return 2
def z(): order.append('z'); return {'b': 3}

d = {**x(), 'k': y(), **z()}
assert order == ['x', 'y', 'z']
assert d == {'a': 1, 'k': 2, 'b': 3}
print('PASS')
