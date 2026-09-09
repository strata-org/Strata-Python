# F-string evaluation order: expressions and format specs in source order.
"""F-string evaluation order: expressions and format specs in source order."""
order = []
def x(): order.append('x'); return 42
def y(): order.append('y'); return 'hello'
def w(): order.append('w'); return 10

result = f"{x():{w()}} {y()}"
assert order == ['x', 'w', 'y']
print('PASS')
