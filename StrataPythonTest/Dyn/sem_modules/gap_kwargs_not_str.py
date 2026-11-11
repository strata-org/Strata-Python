# A call of a built-in with a keyword that is not a str stops with a gap.
try:
    len(**{"q": 1, 1: 2})
except TypeError as e:
    print("TypeError:", e)
