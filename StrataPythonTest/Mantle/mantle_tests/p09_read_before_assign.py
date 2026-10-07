# A name assigned anywhere in a function is local throughout, so reading it before the
# assignment raises UnboundLocalError, whether or not a global of that name exists.
x = 1


def with_global():
    print(x)
    x = 2


def without_global():
    print(y)
    y = 2
