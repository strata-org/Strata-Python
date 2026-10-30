class Other:
    class _Helper:
        pass

class C:
    def __init__(self) -> None:
        self.helper = self._Helper()
