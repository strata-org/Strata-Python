from typing import Union


def check_region(region: Union[str, None]) -> None:
    assert region != "local", "region must not be local"


def check_if_local(region: Union[str, None], n: int) -> None:
    if region == "local":
        assert n >= 1, "n must be positive when local"
