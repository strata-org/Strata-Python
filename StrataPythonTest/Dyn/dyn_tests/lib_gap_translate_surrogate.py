# A translate table that maps to a lone surrogate stops with a gap: the model's strings can't
# hold one.
print(len("a".translate({97: 0xD800})))
