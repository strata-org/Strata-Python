from typing import Dict

@modifies(lambda d: d["k"])
@admit(lambda d, result: d["k"] >= OLD(d["k"]))
def f(d: Dict[str, int]) -> None:
    ...

@modifies(lambda d: d["k"])
@admit(lambda d, result: len(d["k"]) >= OLD(len(d["k"])))
def g(d: Dict[str, str]) -> None:
    ...
