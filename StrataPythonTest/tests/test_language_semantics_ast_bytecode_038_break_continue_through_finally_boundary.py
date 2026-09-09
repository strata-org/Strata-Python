# Boundary: return in finally replaces pending break.
"""Boundary: return in finally replaces pending break."""
def f():
    for i in range(5):
        try:
            break  # pending break
        finally:
            return 'finally_wins'  # replaces break
    return 'loop_done'

assert f() == 'finally_wins'
print('PASS: return in finally replaces pending break')
