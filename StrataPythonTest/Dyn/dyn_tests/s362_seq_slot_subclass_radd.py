# A subclass of list with its own __radd__: CPython then calls list's + slot through the number
# protocol, which raises, instead of the other operand's __radd__; the model stops with a gap.
class R:
    def __radd__(self, o):
        return "R.radd"
class M(list):
    def __radd__(self, o):
        return "M.radd"
try:
    print(M([1]) + R())
except TypeError as e:
    print("TypeError", e)
