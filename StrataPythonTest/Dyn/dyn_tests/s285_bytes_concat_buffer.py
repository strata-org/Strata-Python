# Test: a bytes concatenation with an object whose class defines __buffer__
class B:
    def __buffer__(self, flags):
        return memoryview(b"x")
r = b"a" + B()
