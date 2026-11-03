# Test: the note of an exception from __set_name__ cuts a long class name at 100 characters
class D:
    def __set_name__(self, owner, name):
        raise ValueError("x")
class AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA:
    d = D()
