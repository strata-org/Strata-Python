# Global declaration makes name global for entire body.
"""Global declaration makes name global for entire body."""
x = 'global_val'
def f():
    global x
    x = 'modified'

f()
assert x == 'modified'
print('PASS')
