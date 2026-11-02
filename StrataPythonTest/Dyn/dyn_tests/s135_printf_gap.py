# Test: str % x with a right operand that has __rmod__ stops with a gap until printf-style formatting exists
class P:
    def __rmod__(self, o):
        return "R"
s = "x"
s %= P()
print(s)
