# `super()` in a method reads the implicit `__class__` cell of the class.
class A:
    def m(self):
        return super().m()


class B(A):
    def m(self):
        def inner():
            return __class__
        return inner()
