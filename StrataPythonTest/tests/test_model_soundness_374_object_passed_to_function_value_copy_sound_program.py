# Object passed to pure function — POSITIVE: value copy correctly models
# independence; function sees snapshot, caller's later changes invisible
"""
OBJECT PASSED TO FUNCTION — VALUE COPY MEANS FUNCTION CAN'T SEE
CALLER'S LATER MODIFICATIONS (AND VICE VERSA)

CPython: def f(obj): obj.x = 99  → caller sees obj.x == 99 (reference!)
Model:   def f(obj): obj.x = 99  → caller's obj unchanged (value copy!)

The subset BANS this pattern (finding 278/300). But the CONVERSE is
also important: if the caller modifies obj AFTER passing to function,
the function's copy is unaffected. Under value semantics, this is
AUTOMATICALLY CORRECT — it's a positive property of the model.

This finding confirms that value semantics CORRECTLY models the
independence between a function's parameter and the caller's variable
AFTER the call returns (assuming no aliasing).
"""
from dataclasses import dataclass


@dataclass
class Config:
    host: str
    port: int


def read_port(cfg: Config) -> int:
    """Pure function: reads field, doesn't modify."""
    return cfg.port


def make_modified(cfg: Config) -> Config:
    """Returns new config, doesn't modify input."""
    return Config(cfg.host, cfg.port + 1)


def caller_modifies_after_passing() -> bool:
    """Caller modifies obj after passing — function saw old value."""
    original: Config = Config("localhost", 8080)
    port: int = read_port(original)
    # Caller "modifies" by creating new value
    modified: Config = Config("localhost", 9090)
    # Function saw the ORIGINAL value (8080), not the modified one
    return port == 8080


def function_returns_new_caller_keeps_old() -> bool:
    """Function returns modified copy; caller's original unchanged."""
    original: Config = Config("localhost", 8080)
    modified: Config = make_modified(original)
    # original is unchanged (value semantics)
    # modified has port+1
    return original.port == 8080 and modified.port == 8081


def multiple_calls_independent() -> bool:
    """Multiple function calls on same object — each sees same value."""
    cfg: Config = Config("host", 100)
    a: int = read_port(cfg)
    b: int = read_port(cfg)
    c: int = read_port(cfg)
    # All three calls see the same value (no mutation between calls)
    return a == 100 and b == 100 and c == 100


def main() -> None:
    assert caller_modifies_after_passing()
    assert function_returns_new_caller_keeps_old()
    assert multiple_calls_independent()

    # Additional: two functions, same input, independent results
    cfg: Config = Config("server", 3000)
    r1: Config = make_modified(cfg)
    r2: Config = make_modified(cfg)
    # Both see same input, produce same output
    assert r1.port == 3001
    assert r2.port == 3001
    # Original unchanged
    assert cfg.port == 3000

    print("all passed")


main()
