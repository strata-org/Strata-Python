# Test: super() and type() with keywords
class A:
    pass
a = A()
try:
    s = super(A, a, k=1)
    print("made")
except TypeError as e:
    print("TE", e.args[0])
try:
    type(5, x=1)
except TypeError as e:
    print("TE2", e.args[0])
