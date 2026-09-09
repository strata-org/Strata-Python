# Exception flows into field access — `exception(...).field` accesses
# classname/attrs on wrong constructor tag; undefined behavior
"""
EXCEPTION FLOWS INTO FIELD ACCESS — UNDEFINED BEHAVIOR ON WRONG TAG

CPython: If f() raises, then f().x never executes — exception propagates.
Model:   If f() returns exception(...), then accessing .x on exception tag
         means: classname(exception(...)) → UNDEFINED (wrong constructor)
         or: DictStrAny_get(???, "x") → accessing non-existent attrs

The exception-as-value model (finding 274) means exceptions don't propagate
automatically. They flow as VALUES into subsequent operations. Finding 079
covers exception in OPERATORS (PAdd etc). This finding covers exception
flowing into FIELD ACCESS and METHOD CALLS — a different code path.
"""
from dataclasses import dataclass


@dataclass
class Config:
    host: str
    port: int


def get_config(valid: bool) -> Config:
    if not valid:
        raise ValueError("invalid config")
    return Config("localhost", 8080)


def get_host(valid: bool) -> str:
    """Field access on potentially-exception value."""
    cfg: Config = get_config(valid)
    # If valid=False: get_config raises → cfg = exception(ValueError)
    # Then cfg.host accesses classname/attrs on exception tag → UNDEFINED
    return cfg.host


def get_port_plus_one(valid: bool) -> int:
    """Method-like operation on potentially-exception value."""
    cfg: Config = get_config(valid)
    # cfg might be exception(...) — accessing .port is undefined
    return cfg.port + 1


def chain_access(valid: bool) -> str:
    """Chained field access where first call may raise."""
    cfg: Config = get_config(valid)
    host: str = cfg.host
    # If cfg is exception, host is undefined
    # Then len(host) operates on undefined value
    result: int = len(host)
    return str(result)


def main() -> None:
    # Test 1: valid path works
    assert get_host(True) == "localhost"
    assert get_port_plus_one(True) == 8081

    # Test 2: invalid path must raise, not produce garbage
    raised: bool = False
    try:
        bad: str = get_host(False)
    except ValueError:
        raised = True
    # CPython: raised == True (exception propagates from get_config)
    # Model: raised == False (exception flows into cfg.host as garbage)
    assert raised

    # Test 3: exception in arithmetic chain
    raised2: bool = False
    try:
        bad2: int = get_port_plus_one(False)
    except ValueError:
        raised2 = True
    assert raised2

    # Test 4: chained access
    raised3: bool = False
    try:
        bad3: str = chain_access(False)
    except ValueError:
        raised3 = True
    assert raised3

    print("all passed")


main()
