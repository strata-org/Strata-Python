# Test: a bytes constant % a tuple display stays a %, which CPython never rewrites
a = 1
b = 2
print(b'%d %d' % (a, b))
