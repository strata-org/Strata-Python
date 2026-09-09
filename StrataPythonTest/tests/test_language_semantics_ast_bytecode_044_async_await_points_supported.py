# Async with has await on __aenter__ and __aexit__.
"""Async with has await on __aenter__ and __aexit__."""
import dis
code = compile('async def f():\n  async with ctx() as v:\n    pass', '<t>', 'exec')
f_code = code.co_consts[0]
opcodes = [i.opname for i in dis.get_instructions(f_code)]
# Should have multiple GET_AWAITABLE (one for __aenter__, one for __aexit__)
count = opcodes.count('GET_AWAITABLE')
assert count >= 2, f'got {count}'
print('PASS')
