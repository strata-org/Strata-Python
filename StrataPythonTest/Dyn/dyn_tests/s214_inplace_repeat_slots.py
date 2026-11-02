# Test: in-place repetition, where the left operand's type has sequence slots without a repetition
class A:
    def __index__(self): return 2
o = A()
try:
    o *= [1]
    print(len(o))
except TypeError as e:
    print("TypeError")
d = {}
try:
    d *= [1]
except TypeError as e:
    m1 = e.args[0]
s = {1}
try:
    s *= [1]
except TypeError as e:
    m2 = e.args[0]
r = range(2)
try:
    r *= [1]
except TypeError as e:
    m3 = e.args[0]
class B:
    pass
b = B()
try:
    b *= [1]
except TypeError as e:
    m4 = e.args[0]
print(m1)
print(m2)
print(m3)
print(m4)
n = 2
n *= [1]
print(len(n))
