# `type` statements and type parameters are rejected.  A type alias in a class body is not
# listed among the class's bindings.
type Alias = int


def f[T](x):
    return x


class C:
    type T = int
