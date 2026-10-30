from typing import Dict

@modifies(lambda d: d["a"]["k"])
def f(d: Dict[str, Dict[str, int]]) -> None:
    ...
