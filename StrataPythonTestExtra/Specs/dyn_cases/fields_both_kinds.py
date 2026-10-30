# The class body's declaration goes into py.fields, and the field that __init__ assigns goes
# into py.initFields.
class C:
    class _Helper:
        pass

    count: int

    def __init__(self) -> None:
        self.helper = self._Helper()
