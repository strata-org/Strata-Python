class C:
    def ensures(self, p: int) -> int:
        ...

    @ensures(lambda self, result: result > 0)
    def m(self) -> int:
        ...
