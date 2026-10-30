# y reads m before the method m is bound, and the module binds no m, so CPython raises NameError.
class C:
    y = m
    def m(self) -> int:
        ...
