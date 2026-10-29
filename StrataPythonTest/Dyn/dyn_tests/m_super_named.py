# A module that names `super` makes CPython compile every super().x as a plain call, so a
# deleted first parameter raises RuntimeError before the cell is read.
s = super


class A:
    def m(self):
        return 0


class B(A):
    def attr_del(self):
        del self
        return super().m()
