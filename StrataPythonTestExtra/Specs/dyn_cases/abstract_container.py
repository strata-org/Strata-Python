from typing import Mapping

@modifies(lambda d: d["k"])
def f(d: Mapping[str, int]) -> None:
    ...
