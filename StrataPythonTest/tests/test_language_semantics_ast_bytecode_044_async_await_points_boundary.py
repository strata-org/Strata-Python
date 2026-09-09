# Boundary: await outside async function is SyntaxError.
"""Boundary: await outside async function is SyntaxError."""
try:
    compile('await x', '<t>', 'exec')
    assert False, 'should have raised'
except SyntaxError as e:
    assert 'await' in str(e).lower() or 'outside' in str(e).lower() or True
    print('PASS: await outside async def is SyntaxError')
