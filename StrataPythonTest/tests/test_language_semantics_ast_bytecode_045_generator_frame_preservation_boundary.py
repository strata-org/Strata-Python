# Boundary: send() delivers value as yield expression result.
"""Boundary: send() delivers value as yield expression result."""
def gen():
    received = yield 'first'
    yield f'got:{received}'

g = gen()
assert next(g) == 'first'
assert g.send('hello') == 'got:hello'
print('PASS: send() value becomes yield expression result (frame state includes stack)')
