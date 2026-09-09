# Nested object composition (`svc.config = cfg`) — value model copies inner
# object; mutations through one path invisible through other
"""
When a class instance is stored as a field of another instance, both the
outer.inner reference and the original variable point to the SAME object
in CPython. Mutating through one path is visible through the other.
In the value model, from_ClassInstance contains a COPY of the inner value —
mutations through one path are invisible through the other.
"""
from dataclasses import dataclass


@dataclass
class Config:
    timeout: int


@dataclass
class Service:
    name: str
    config: Config


def update_timeout(cfg: Config, new_val: int) -> None:
    cfg.timeout = new_val


def main() -> None:
    cfg: Config = Config(timeout=30)
    svc: Service = Service(name="api", config=cfg)

    # cfg and svc.config are the SAME object in CPython
    update_timeout(cfg, 60)

    # CPython: svc.config.timeout == 60 (same object was mutated)
    # Model: svc.config.timeout == 30 (svc holds a copy of the old value)
    assert svc.config.timeout == 60

    # Direct field mutation through nested access
    svc.config.timeout = 90
    # CPython: cfg.timeout == 90 (same object)
    # Model: cfg is unchanged (svc.config is a separate value)
    assert cfg.timeout == 90

    print(svc.config.timeout, cfg.timeout)


main()
