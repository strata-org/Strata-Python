# A class binding a name that a method reads from the enclosing function.
def f():
    x = 1

    class C:
        x = 2

        def m(self):
            return x
    return C
