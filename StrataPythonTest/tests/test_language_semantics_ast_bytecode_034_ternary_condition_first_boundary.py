# Boundary: naive L-to-R would evaluate x before condition.
"""Boundary: naive L-to-R would evaluate x before condition."""
order = []
def explode(): order.append('BOOM'); raise RuntimeError('should not run')
def cond(): order.append('cond'); return False
def safe(): order.append('safe'); return 'ok'

# If naive L-to-R: explode() would run first → RuntimeError
# CPython: cond() first, then safe() (skips explode)
result = explode() if cond() else safe()
assert order == ['cond', 'safe'], f'got {order}'
print('PASS: true-branch not evaluated when condition is false')
