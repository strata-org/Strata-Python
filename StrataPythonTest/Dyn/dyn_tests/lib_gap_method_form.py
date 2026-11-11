# A wrong call of a METH_NOARGS method through a stored bound method of a str subclass names the
# subclass, an immediate call names str: the model can't tell them apart, so it stops with a gap.
class S(str):
    pass


f = S("a").upper
try:
    f(1)
except TypeError as e:
    print(e)
