# A model whose constructor has a contract. The Laurel front ends do not check it at
# any call yet (card "Laurel front ends: Check model constructor contracts").
class K:
    @requires(lambda region: len(region) <= 3)
    def __init__(self, region: str) -> None:
        assert len(region) >= 1, "region must not be empty"

    def m(self) -> None:
        ...


def use(k: K) -> None:
    ...
