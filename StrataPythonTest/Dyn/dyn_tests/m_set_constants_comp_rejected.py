# Test: a set display of constants that the translator rejects, as the source of a later "for"
# clause of a comprehension. CPython's AST optimizer folds "1 + 2" into a constant first, so the
# display is a frozenset constant.
a = [x for y in [1] for x in {1 + 2, 9}]
