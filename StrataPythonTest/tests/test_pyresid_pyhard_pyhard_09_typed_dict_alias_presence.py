from typing import NotRequired, TypedDict


class Settings(TypedDict):
    service: str
    retries: NotRequired[int]


def direct_update(settings: Settings, retries: int) -> int:
    settings["retries"] = retries
    return settings.get("retries")


def alias_update(settings: Settings, retries: int) -> int | None:
    alias = settings
    alias["retries"] = retries
    return settings.get("retries")
