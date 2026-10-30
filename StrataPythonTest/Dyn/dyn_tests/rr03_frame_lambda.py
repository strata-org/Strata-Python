# A lambda that reads its frame's locals through `locals()`, which is given no cells: ref-to-reg
# promotes the lambda's cell although `locals()` observes it.
g = lambda x: locals()
