class Resource:
    def __init__(self, value: int):
        self.value: int = value

    def __enter__(self) -> int:
        return self.value

    def __exit__(self, *args) -> bool:
        return True


entered: int = 0


def bind_entered():
    global entered
    resource: Resource = Resource(8)
    with resource as entered:
        pass


bind_entered()
assert entered == 8, "global with-as target is updated"
