# Test: repr, str, ascii and format through user __repr__, __str__ and __format__, and their errors
class C:
    def __repr__(self):
        return "C!"
class D:
    def __str__(self):
        return "D-str"
    def __repr__(self):
        return "D-repr"
print(C(), [C(), D()], f"{D()!s}", repr(D()))
print(f"{C()!r} {D()} {D()!r} {D()!s} {3:>5} {2.5:.3f} {'ab':^6}|")
class E:
    def __repr__(self):
        return 5
try:
    repr(E())
except TypeError as e:
    print(e)
try:
    f"{E()!s}"
except TypeError as e:
    print(e)
class F:
    def __format__(self, spec):
        return "F:" + spec
print(f"{F():xyz}")
try:
    f"{object():x}"
except TypeError as e:
    print(e)
print(int.__repr__(True), object.__str__(5), f"{"é"!a} {[1, "ü"]!a}")
