# Test: a TypeError of __length_hint__'s descriptor propagates; one of the call means no hint
class D:
    def __get__(self, obj, cls):
        raise TypeError("from __get__")


class C:
    __length_hint__ = D()

    def __iter__(self):
        return iter([1])


try:
    print(len([*C()]))
except TypeError as e:
    print("TypeError", e.args[0])


class E:
    def __length_hint__(self):
        raise TypeError("from the call")

    def __iter__(self):
        return iter([1, 2])


print(len([*E()]))
