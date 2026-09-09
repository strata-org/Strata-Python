# Boundary: break exits loop but __exit__ still runs.
"""Boundary: break exits loop but __exit__ still runs."""
order = []
class CM:
    def __enter__(self): order.append('enter'); return self
    def __exit__(self, *a): order.append('exit'); return False

for i in range(5):
    with CM():
        order.append(f'body{i}')
        if i == 0:
            break

# Naive model might skip __exit__ on break
assert order == ['enter', 'body0', 'exit'], f'got {order}'
print('PASS: __exit__ not skipped by break (naive model would miss it)')
