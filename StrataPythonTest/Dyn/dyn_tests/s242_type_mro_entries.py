# Test: type() with a base that has __mro_entries__ raises CPython's TypeError
class E:
    def __mro_entries__(self, bases):
        return (object,)
X = type("X", (E(),), {})
