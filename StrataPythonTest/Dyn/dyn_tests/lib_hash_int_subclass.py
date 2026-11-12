# A __hash__ that returns an instance of a subclass of int: CPython 3.12 accepts any int.
class I(int):
    pass


class A:
    def __hash__(self):
        return I(9)


try:
    print(hash(A()))
except TypeError as e:
    print("TypeError", e)
