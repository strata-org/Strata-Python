# A stub __init__ with *args is rejected like any other method, so the whole
# model is rejected.
class C:
    def __init__(self, *args, **kwargs) -> None:
        ...
