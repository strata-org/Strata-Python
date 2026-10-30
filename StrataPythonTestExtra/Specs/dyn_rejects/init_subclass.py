class B:
    def __init_subclass__(cls) -> None: ...

class C(B):
    pass
