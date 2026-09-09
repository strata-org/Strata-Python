# Ternary: only one branch evaluated.
"""Ternary: only one branch evaluated."""
order = []
def true_branch(): order.append('true'); return 'T'
def false_branch(): order.append('false'); return 'F'
def cond(): order.append('cond'); return False

result = true_branch() if cond() else false_branch()
assert order == ['cond', 'false']
assert result == 'F'
print('PASS')
