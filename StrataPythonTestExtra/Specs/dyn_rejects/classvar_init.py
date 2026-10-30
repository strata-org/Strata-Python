def g() -> None:
    ...

class C:
    __init__ = g
    __getattr__ = g
