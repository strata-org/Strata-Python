# Dataclass default field values — `Config(host="x")` omitting `port: int =
# 8080` may not substitute the default
"""
@dataclass fields can have default values: `field: int = 0`. When
constructing an instance without providing that argument, the default
is used. The model must know that:
1. The default value is substituted when the argument is omitted
2. The resulting ClassInstance has the field set to the default

If the translator doesn't handle dataclass defaults, construction with
omitted arguments either fails or produces Hole for the missing field.
"""
from dataclasses import dataclass


@dataclass
class Config:
    host: str
    port: int = 8080
    timeout: int = 30
    debug: bool = False


@dataclass
class Counter:
    name: str
    value: int = 0


def create_default_config() -> Config:
    # Only host is required; port, timeout, debug use defaults
    return Config(host="localhost")


def create_custom_config() -> Config:
    return Config(host="prod.example.com", port=443, timeout=60, debug=False)


def create_counter(name: str) -> Counter:
    return Counter(name=name)  # value defaults to 0


def main() -> None:
    # Default values used
    cfg: Config = create_default_config()
    assert cfg.host == "localhost"
    assert cfg.port == 8080      # default
    assert cfg.timeout == 30     # default
    assert cfg.debug == False    # default

    # Custom values override defaults
    cfg2: Config = create_custom_config()
    assert cfg2.port == 443
    assert cfg2.timeout == 60

    # Counter with default value
    c: Counter = create_counter("hits")
    assert c.name == "hits"
    assert c.value == 0  # default

    # Partial override
    c2: Counter = Counter(name="errors", value=5)
    assert c2.value == 5

    print(cfg.port, cfg.timeout, c.value)


main()
