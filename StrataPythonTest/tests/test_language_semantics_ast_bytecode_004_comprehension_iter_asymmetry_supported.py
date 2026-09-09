# Outermost iterable sees enclosing scope; body is isolated
items = [1, 2, 3]
result = [x * 2 for x in items]  # 'items' resolved in enclosing scope
assert result == [2, 4, 6]
assert 'x' not in dir() or x != 3  # x doesn't leak (3.x)
print("OK: comprehension iter asymmetry — items visible, x isolated")
