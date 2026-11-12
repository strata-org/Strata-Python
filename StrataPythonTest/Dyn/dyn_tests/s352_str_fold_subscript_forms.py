# A % whose left operand CPython's AST optimizer folds to a str through a subscript that isn't of a
# tuple display at a non-negative int literal (a negative, boolean or computed index, a nested
# subscript, a subscript of a product) is a format that the optimizer rewrites into an f-string; the
# translator rejects each one.
x = 1
print(("%s",)[-1] % (x,))
print((1, "%s")[True] % (x,))
print((("%s",),)[0][0] % (x,))
print((("%s",) * 2)[1] % (x,))
print(("%s",)[1 - 1] % (x,))
print((1, "%s")[__debug__] % (x,))
