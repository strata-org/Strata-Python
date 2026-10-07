# Call-boundary errors. Each message mirrors CPython's, with two expected
# differences:
#
#  1. The qualified name is this module rather than __main__, because the script
#     is translated as a named module. CPython would say __main__.f().
#  2. For `*x`, CPython has two lowerings with two different messages: a single
#     starred argument passes the operand straight to the call and reports
#     "f() argument after * must be an iterable", while any other combination
#     builds a list first and reports the unqualified "Value after * must be an
#     iterable". This IR always builds a tuple, so it always produces the second
#     message -- the correct message for the lowering it uses.
def f(**kwargs):
    print("unreachable")

m = {"a": 1}
try:
    f(**m, **m)
except TypeError as e:
    print("dup:", e)

try:
    f(**{1: 2})
except TypeError as e:
    print("nonstr:", e)

try:
    f(**[1])
except TypeError as e:
    print("nonmap:", e)

def g(*args):
    print("unreachable")
try:
    g(*5)
except TypeError as e:
    print("noniter:", e)
