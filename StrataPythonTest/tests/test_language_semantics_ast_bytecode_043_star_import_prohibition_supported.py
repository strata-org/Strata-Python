# Star import at module level is fine.
"""Star import at module level is fine."""
code = compile('from os.path import *', '<t>', 'exec')
assert code is not None
print('PASS')
