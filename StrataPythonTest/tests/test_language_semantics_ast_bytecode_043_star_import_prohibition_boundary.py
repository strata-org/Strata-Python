# Boundary: also prohibited in class body (3.x).
"""Boundary: also prohibited in class body (3.x)."""
try:
    compile('class C:\n  from os import *', '<t>', 'exec')
    # In Python 3, this is also a SyntaxError
    assert False, 'should have raised'
except SyntaxError as e:
    assert 'import *' in str(e)
    print('PASS: import * in class is also SyntaxError')
