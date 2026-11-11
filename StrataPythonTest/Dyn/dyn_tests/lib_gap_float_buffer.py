# float() of an object with __buffer__ stops with a gap.
class Buf:
    def __buffer__(self, flags):
        return memoryview(b"12")


print(float(Buf()))
