class Base:
    class _C:
        pass

class D(Base):
    def _C(self) -> int:
        ...

    def __init__(self) -> None:
        self.f = self._C()
