# A known difference from CPython: the __class__ cell is filled after __build_class__ returns,
# not inside type.__new__.  So hook(), which __init_subclass__ calls while A is created, finds
# the cell empty and raises, where CPython's hook() returns (A, A).
class Base:
    def __init_subclass__(cls):
        cls.hook()

    @classmethod
    def hook(cls):
        return cls


class A(Base):
    @classmethod
    def hook(cls):
        return super().hook(), __class__
