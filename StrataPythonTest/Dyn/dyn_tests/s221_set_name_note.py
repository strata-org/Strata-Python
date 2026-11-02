# Test: an exception from __set_name__ gets CPython 3.12's note
class D:
    def __set_name__(self, owner, name):
        raise ValueError("boom")
try:
    class C:
        x = D()
except ValueError as e:
    n = e.__notes__
    print(n[0])
