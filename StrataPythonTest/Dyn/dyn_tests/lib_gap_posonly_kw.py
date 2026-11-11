# A keyword to a positional-only method through a stored bound method of a list subclass names
# the subclass, an immediate call names list: the model can't tell them apart, so it stops with
# a gap.
class L(list):
    pass


f = L([1]).pop
try:
    f(x=1)
except TypeError as e:
    print(e)
