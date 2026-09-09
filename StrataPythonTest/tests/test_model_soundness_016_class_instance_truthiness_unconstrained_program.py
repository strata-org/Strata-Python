# `Any_to_bool` returns Hole for `from_ClassInstance`; CPython always returns
# True (no `__bool__`/`__len__` in subset)
"""
Python objects without __bool__ or __len__ are ALWAYS truthy.
The Laurel encoding's Any_to_bool returns Hole (unconstrained) for
from_ClassInstance, so the solver treats instance truthiness as unknown.
"""
from dataclasses import dataclass


@dataclass
class Config:
    name: str
    value: int


def is_configured(cfg: Config) -> bool:
    # In Python, `if cfg` is always True for a class instance
    # (no __bool__ or __len__ defined)
    if cfg:
        return True
    return False


def select(cfg: Config, fallback: str) -> str:
    # `cfg or fallback` — since cfg is always truthy, always returns cfg.name
    # But the model doesn't know cfg is truthy
    result: str = cfg.name if cfg else fallback
    return result


def main() -> None:
    c: Config = Config(name="prod", value=42)

    # CPython: always True (class instances are truthy)
    assert is_configured(c) == True

    # CPython: always "prod" (cfg is truthy, so ternary takes true branch)
    assert select(c, "default") == "prod"

    print(is_configured(c))
    print(select(c, "default"))


main()
