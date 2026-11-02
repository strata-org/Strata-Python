# Test: __init_subclass__ of a base and of a middle class, chained through super().__init_subclass__
class Base:
    def __init_subclass__(cls, **kw):
        super().__init_subclass__(**kw)
        print("base", cls.__name__)
class Mid(Base):
    def __init_subclass__(cls, **kw):
        super().__init_subclass__(**kw)
        print("mid", cls.__name__)
class Leaf(Mid):
    pass
