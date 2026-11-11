# dict.fromkeys of a set whose order the model doesn't know (a set of strs, whose hashes depend
# on the seed) stops with a gap: the dict's order would come from the set's.
a, b = "a", "b"
print(dict.fromkeys(set([a, b])))
