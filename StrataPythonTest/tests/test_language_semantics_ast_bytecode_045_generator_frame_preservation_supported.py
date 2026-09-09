# Generator preserves exception state across yields.
"""Generator preserves exception state across yields."""
def gen():
    try:
        yield 'in_try'
        raise ValueError('from_gen')
    except ValueError:
        yield 'in_except'
        yield 'still_in_except'

g = gen()
assert next(g) == 'in_try'
assert next(g) == 'in_except'
assert next(g) == 'still_in_except'
print('PASS')
