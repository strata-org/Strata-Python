from typing import overload

# The @overload stubs of __init__ are recorded, and they get no Laurel procedure.
class C:
    @overload
    def __init__(self, x: int) -> None:
        ...

    @overload
    def __init__(self, x: str) -> None:
        ...
