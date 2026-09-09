# Boundary: assignment before nonlocal is SyntaxError.
"""Boundary: assignment before nonlocal is SyntaxError."""
try:
    compile('def outer():\n  x=1\n  def inner():\n    x=2\n    nonlocal x', '<t>', 'exec')
    assert False, 'should have raised'
except SyntaxError as e:
    assert 'assigned to before nonlocal' in str(e).lower() or 'is assigned' in str(e)
    print('PASS: SyntaxError for assign before nonlocal')
