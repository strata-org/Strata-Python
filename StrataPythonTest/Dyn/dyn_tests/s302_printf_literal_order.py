# Test: a literal % with a tuple display runs as the f-string CPython 3.12 makes of it, each item formatted before the next is evaluated
class A:
    def __str__(self):
        print("str A")
        return "a"
    def __repr__(self):
        print("repr A")
        return "A"
def g():
    print("g")
    return 2
print('%s %s' % (A(), g()))
print('%r|%5s|%-5s|%.1s|%a' % (A(), g(), g(), A(), A()))
fmt = '%s %s'
print(fmt % (A(), g()))
print('%d %s' % (g(), A()))
print('x%%y %s' % (A(),))
print('%s' % (A(),))
print('' % ())
print('%s %s' % (1, 2))
print('%+s %05s' % (A(), A()))
try:
    print('%s %s' % (A(),))
except TypeError as e:
    print(e)
