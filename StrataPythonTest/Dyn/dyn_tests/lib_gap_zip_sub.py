# A subclass of zip stops with a gap.
class Z(zip):
    pass


print("before")
print(type(Z([1], [2])).__name__)
