# A key of str.maketrans that is an instance of a subclass of int stops with a gap.
class I(int):
    pass


print(str.maketrans({I(97): "b"}))
