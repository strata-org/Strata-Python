# A % whose left operand folds to an int, not a str, is no format: CPython's AST optimizer leaves
# it alone, and it raises TypeError at run time, as here.
x = 5
for f in [lambda: (-1) % (x,), lambda: (1 + 2) % (x, x), lambda: (2 ** 8) % (x,)]:
    try:
        f()
    except TypeError as e:
        print("TypeError", e)
