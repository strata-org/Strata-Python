class Resource:
    def __init__(self, value: int):
        self.value: int = value

    def __enter__(self) -> int:
        return self.value

    def __exit__(self, *args) -> bool:
        return True


resource: Resource = Resource(8)
with resource as entered:
    pass


def read_entered() -> int:
    return entered


assert read_entered() == 8, "with-as target creates module field"
