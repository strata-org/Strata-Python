# zip.__new__ with a subclass stops with a gap.
class Z(zip):
    pass


print("before")
print(type(zip.__new__(Z, [1])).__name__)
