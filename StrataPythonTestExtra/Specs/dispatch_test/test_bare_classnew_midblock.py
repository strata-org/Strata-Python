class Registry:
    def __init__(self, name: str) -> None: ...


def use_it() -> bool:
    Registry("first")
    return True
