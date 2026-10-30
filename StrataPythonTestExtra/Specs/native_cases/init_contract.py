# A stub's __init__ is read like any other method: its typed parameters, its body
# asserts and its decorators give the method `__init__`. Its top-level
# `self.f = self._C()` assignment still declares the field `f`; such an assignment
# nested in an `if` declares no field.
class C:
    count: int

    class _Helper:
        pass

    @requires(lambda region: len(region) <= 10)
    @modifies(lambda self: self.count)
    @admit(lambda region, result: len(region) >= 2)
    def __init__(self, region: str, n: int) -> None:
        assert len(region) >= 1, "region must not be empty"
        self.helper = self._Helper()
        if n > 0:
            self.extra = self._Helper()
            assert n <= 3, "n is small"
