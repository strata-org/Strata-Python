# Dataclass partial construction — omitted fields with defaults must be
# substituted at call site; generated __init__ defaults not in AST
"""
When a @dataclass has a field with a default value that is a mutable
container (list/dict), Python's dataclass machinery uses default_factory
to create a fresh copy per instance. But if the default is a LITERAL
in the class body (not field(default_factory=...)), Python raises
ValueError at class definition time.

However, the REAL issue for Laurel is simpler: even with immutable
defaults (int, str, None), the model must correctly substitute defaults
when fewer arguments are passed to the constructor.

This finding focuses on: @dataclass constructor with PARTIAL arguments
where some fields use defaults. The model must substitute the default
values for omitted fields.

Uses ONLY confirmed-accepted constructs: @dataclass, int, str, Optional,
function def.
"""
from dataclasses import dataclass
from typing import Optional


@dataclass
class Config:
    host: str
    port: int = 8080
    timeout: int = 30
    debug: bool = False


@dataclass
class Request:
    method: str
    path: str
    body: Optional[str] = None


def create_default_config() -> Config:
    # Only host is required; port, timeout, debug use defaults
    c: Config = Config(host="localhost")
    return c


def create_partial_config() -> Config:
    # host and port specified; timeout and debug use defaults
    c: Config = Config(host="example.com", port=9090)
    return c


def check_defaults() -> bool:
    c: Config = Config(host="test")
    # These must all hold — defaults were substituted
    return c.port == 8080 and c.timeout == 30 and c.debug == False


def request_without_body() -> bool:
    r: Request = Request(method="GET", path="/api")
    # body defaults to None
    return r.body is None


def request_with_body() -> bool:
    r: Request = Request(method="POST", path="/api", body="data")
    return r.body == "data"


def main() -> None:
    c1: Config = create_default_config()
    assert c1.host == "localhost"
    assert c1.port == 8080
    assert c1.timeout == 30
    assert c1.debug == False

    c2: Config = create_partial_config()
    assert c2.host == "example.com"
    assert c2.port == 9090
    assert c2.timeout == 30  # default
    assert c2.debug == False  # default

    assert check_defaults() == True
    assert request_without_body() == True
    assert request_with_body() == True

    print(c1.port, c2.port, c1.timeout)


main()
