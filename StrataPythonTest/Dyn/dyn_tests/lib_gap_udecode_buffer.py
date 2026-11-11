# A UnicodeDecodeError of an object with __buffer__ stops with a gap.
class Buf:
    def __buffer__(self, flags):
        return memoryview(b"xy")


print(UnicodeDecodeError("u", Buf(), 0, 1, "r").object)
