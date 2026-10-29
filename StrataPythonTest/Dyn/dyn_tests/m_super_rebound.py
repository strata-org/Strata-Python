# A module that rebinds super: CPython then calls it with no arguments, which the translator
# rejects.
super = print


class A:
    def m(self):
        return super()
