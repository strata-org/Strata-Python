# A __float__ that returns an instance of a float subclass warns: a gap.
class F(float):
    pass


class A:
    def __float__(self):
        return F(1.5)


print("before")
x = float(A())
