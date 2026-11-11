# An __int__ that returns an instance of a subclass of int warns: a gap.
class I(int):
    pass


class A:
    def __int__(self):
        return I(3)


print("before")
x = int(A())
