# A bound built-in method's argument error names its type when it is called as a method, and the
# type of self when the bound method is called later; the IR doesn't show which, so an error on an
# instance of a subtype stops with a gap.
class E(Exception):
    pass
try:
    BaseException().add_note()
except TypeError as e:
    print(e)
g = E().add_note
try:
    g()
except TypeError as e:
    print(e)
