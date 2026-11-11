# An int subclass instance of a hash whose number the model does not know stops with a gap.
class I(int):
    pass


print("before")
x = I(hash("a"))
