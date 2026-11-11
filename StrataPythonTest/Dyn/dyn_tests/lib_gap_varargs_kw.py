# A keyword to str.find names "str.find()" in a method call and "find()" through a stored bound
# method: the model can't tell them apart, so it stops with a gap.
try:
    "abc".find("a", x=1)
except TypeError as e:
    print(e)
