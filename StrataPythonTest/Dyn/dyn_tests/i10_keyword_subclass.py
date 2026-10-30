# Keywords that are instances of a str subclass. CPython 3.12 compares each keyword with each
# parameter name by ==, not by a dict lookup: the first call raises the RuntimeError of
# RaisingEq.__eq__, and the second prints 1, although OtherHash("p") has another hash than "p".
# Each call site passes the keyword in a dict, and the callee's prologue applies py.bindArgs,
# whose failure edge goes to the function's raise path.
class RaisingEq(str):
    __hash__ = str.__hash__
    def __eq__(self, other):
        raise RuntimeError("raised by __eq__ during argument binding")

class OtherHash(str):
    def __hash__(self):
        return 12345
    __eq__ = str.__eq__

def f(p):
    return p

try:
    print(f(**{RaisingEq("p"): 1}))
except RuntimeError as e:
    print("caught:", e)
print(f(**{OtherHash("p"): 1}))
