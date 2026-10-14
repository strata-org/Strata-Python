# A `global super` in any function, with no assignment, also puts `super` in the module's
# symbol table, so super().x is a plain call, as in m_super_named.
def g():
    global super


class A:
    def m(self):
        return 0


class B(A):
    def attr_del(self):
        del self
        return super().m()
