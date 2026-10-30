# c.f on an instance of a model class that declares __getitem__ rejects the model: the read
# may be an item.
class C:
    n: int

    def __getitem__(self, k: str) -> int:
        ...

@admit(lambda c, result: c.n >= 0)
def g(c: C) -> int:
    ...
