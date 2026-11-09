# Test: str % x with a right operand that has __rmod__: str formats, and the __rmod__ never runs
class P:
    def __rmod__(self, o):
        return "R"
s = "x"
s %= P()
print(s)
