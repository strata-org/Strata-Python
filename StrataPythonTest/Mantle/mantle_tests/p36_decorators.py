# Decorators and class bases are evaluated by the enclosing scope.
def deco(fn):
    return fn


def outer(base):
    @deco
    def inner():
        return 1

    class K(base, metaclass=type):
        pass
    return inner, K
