# Zero-argument super() inside two nested comprehensions finds the method's first parameter.
class A:
    def m(self, i):
        return i


class B(A):
    def m(self, rows):
        return [[super().m(i) for i in r] for r in rows]
