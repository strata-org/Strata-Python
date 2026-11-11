# bytes() of an object with __buffer__ stops with a gap.
class B:
    def __buffer__(self, flags):
        return memoryview(b"x")


print("before")
x = bytes(B())
