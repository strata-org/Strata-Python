from typing import Dict

ghost(name="resources", type=Dict[str, int])


# Acquiring changes the ghost table: the post-state contains the key.
@modifies(lambda: resources)
@admit(lambda name, result: name in resources)
def acquire(name: str) -> None:
    ...


@admit(lambda name, result: result == (name in resources))
def exists(name: str) -> bool:
    ...
