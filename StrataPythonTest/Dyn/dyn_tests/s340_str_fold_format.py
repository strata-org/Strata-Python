# A % whose left operand CPython's AST optimizer folds into a str constant, here "%s" + "", or a
# product with a str on one side only, 1 * "%s" or "%s" * 1, is a format that the optimizer
# rewrites into an f-string; the translator rejects each one.
x = 1
print(("%s" + "") % (x,))
print((1 * "%s") % (x,))
print(("%s" * 1) % (x,))
