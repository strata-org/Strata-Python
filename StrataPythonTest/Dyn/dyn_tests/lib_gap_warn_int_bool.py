# An __int__ that returns a bool warns: a gap.
class A:
    def __int__(self):
        return True


print("before")
x = int(A())
