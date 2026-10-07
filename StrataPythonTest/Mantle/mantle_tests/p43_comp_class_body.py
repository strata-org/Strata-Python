# Comprehensions in class bodies: an enclosing function's local they read is free in the
# class; a lambda capturing the iteration variable makes it a cell of the class; `__class__`
# and `super` do not reach the class's `__class__` cell.
def outer(rows):
    scale = 3

    class C:
        k = 1
        a = [r * scale + k for r in rows]
        fs = [lambda: r for r in rows]
        own = [__class__ for _ in rows]

        def m(self):
            return [super() for _ in rows]

    return C
