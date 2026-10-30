# The class body declares `helper` as int, but `__init__` makes it a `_Helper`.
class C:
    class _Helper:
        pass

    helper: int

    def __init__(self) -> None:
        self.helper = self._Helper()
