# A class that defines __init__ twice is rejected.
class C:
    def __init__(self, x: int) -> None:
        ...

    def __init__(self, x: str) -> None:
        ...
