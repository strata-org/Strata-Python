# Test: set displays of constants that the translator rejects
# CPython's AST optimizer folds "1 + 2" into a constant first, so this display is a frozenset
# constant too.
a = {1 + 2, 9, 17}
