from typing import Dict

ghost(name="resources", type=Dict[str, int])
ghost(name="allocated", type=int, init=0)


# Two-state contract: the counter increments relative to its pre-state value.
@modifies(lambda: resources)
@modifies(lambda: allocated)
@admit(lambda name, result: name in resources)
@admit(lambda name, result: allocated == OLD(allocated) + 1)
def acquire(name: str) -> None:
    ...


@admit(lambda result: result == allocated)
def alloc_count() -> int:
    ...


@admit(lambda name, result: result == (name in resources))
def exists(name: str) -> bool:
    ...
