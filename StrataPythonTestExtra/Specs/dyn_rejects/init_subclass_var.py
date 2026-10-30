from typing import Any

def hook(cls: Any) -> None: ...

class B:
    __init_subclass__ = hook

class C(B):
    pass
