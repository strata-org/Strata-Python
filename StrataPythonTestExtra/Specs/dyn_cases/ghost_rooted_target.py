from typing import Dict

ghost(name="table", type=Dict[str, int])

@modifies(lambda: table["k"])
def put() -> None:
    ...
