# Decoding an object with __buffer__ stops with a gap.
class Buf:
    def __buffer__(self, flags):
        return memoryview(b"xy")


print(str(Buf(), "ascii"))
